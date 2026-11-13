import OpenAIGrouped.Unit009
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit007

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorEnergy.lean; sha256: 1650b8b5d4a9ddf458137c7e0904dca8683b4ddd51986d6019cb9893d6c0bad4 -/
section Source400
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorEnergy
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι α ρ : Type*} [DecidableEq ι]

def allocatedPolynomial (D : Ideal O) (s : Finset ι) (T : Finset α)
    (v : α → ι → Ideal O) (F : ρ → α → ℂ) (a : Allocation D s) (h : ρ) : ℂ :=
  ∑ j ∈ T, allocationTerm D s (v j) a*F h j

theorem finite_mask_regroup (D : Ideal O) (hD : Squarefree D) (s : Finset ι)
    (T : Finset α) (v : α → ι → Ideal O) (F : ρ → α → ℂ) (h : ρ) :
    (∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0) =
      ∑ a : Allocation D s, allocatedPolynomial D s T v F a h := by
  have ht (j : α) : (if D∣∏ i ∈ s,v j i then F h j else 0) =
      ∑ a : Allocation D s, allocationTerm D s (v j) a*F h j := by
    have he := congrArg (fun w : ℂ => w*F h j) (squarefree_mask_allocation D hD s (v j))
    simpa only [ite_mul,one_mul,zero_mul,Finset.sum_mul] using he
  simp_rw [ht]
  rw [Finset.sum_comm]
  rfl

theorem allocation_card_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), D ≠ 0 → ∀ s : Finset ι, s.card ≤ N →
      (Fintype.card (Allocation D s):ℝ) ≤ C*(Ideal.absNorm D:ℝ)^ε := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/N) (div_pos hε hNr)
  refine ⟨C^N,pow_pos hC _,?_⟩
  intro D hD s hs
  have hn : 0 ≤ (Ideal.absNorm D:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ((2:ℝ)^(primeSupport D).card)^s.card := by exact_mod_cast allocation_card_bound D s
    _ ≤ ((2:ℝ)^(primeSupport D).card)^N := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hs
    _ ≤ (C*(Ideal.absNorm D:ℝ)^(ε/N))^N := pow_le_pow_left₀ (by positivity) (hb D hD) N
    _ = C^N*(Ideal.absNorm D:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hn]
      congr 2
      field_simp

theorem allocated_energy_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), Squarefree D → ∀ s : Finset ι, s.card ≤ N →
      ∀ (T : Finset α) (v : α → ι → Ideal O) (F : ρ → α → ℂ) (rows : Finset ρ),
      (∑ h ∈ rows, ‖∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a : Allocation D s, ∑ h ∈ rows, ‖allocatedPolynomial D s T v F a h‖^2 := by
  obtain ⟨C,hC,hcard⟩ := allocation_card_small_power (ι := ι) N hN ε hε
  refine ⟨C,hC,?_⟩
  intro D hD s hs T v F rows
  have hrow (h : ρ) : ‖∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0‖^2 ≤
      (Fintype.card (Allocation D s):ℝ)*∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖^2 := by
    rw [finite_mask_regroup D hD s T v F h]
    calc
      _ ≤ (∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _a : Allocation D s => (1:ℝ))
          (fun a => ‖allocatedPolynomial D s T v F a h‖))
  calc
    _ ≤ ∑ h ∈ rows, (Fintype.card (Allocation D s):ℝ)*
        ∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖^2 :=
      Finset.sum_le_sum (fun h _ => hrow h)
    _ = (Fintype.card (Allocation D s):ℝ)*
        ∑ a : Allocation D s, ∑ h ∈ rows, ‖allocatedPolynomial D s T v F a h‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD.ne_zero s hs)
      (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end SevenEighths.CenteredMomentDivisorEnergy

end

end OAI

end Source400

/- Original source: OAI/NumberTheory/DirichletL/Moments/Rankin.lean; sha256: ca3d37208cc7d7e9586e814398a8853ef92645f77eea0436f42567d26bbc50a9 -/
section Source401
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter
namespace SevenEighths.CenteredMomentRankin
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def primeMass (P : Ideal O) (δ : ℝ) : ℝ := ((Ideal.absNorm P:ℝ)^δ-1)⁻¹

theorem prime_norm_ge_two (P : Ideal O) (hp : Prime P) : 2 ≤ Ideal.absNorm P := by
  have h0 := Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero
  have h1 : Ideal.absNorm P ≠ 1 := by
    intro hn
    exact hp.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp hn))
  omega

theorem primeMass_nonneg (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ primeMass P δ := by
  apply inv_nonneg.mpr
  have hn : (1:ℝ) < Ideal.absNorm P := by exact_mod_cast (prime_norm_ge_two P hp)
  exact (sub_pos.mpr (Real.one_lt_rpow hn hδ)).le

theorem primeMass_le_fixed (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    primeMass P δ ≤ ((2:ℝ)^δ-1)⁻¹ := by
  apply inv_anti₀ (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hδ))
  exact sub_le_sub_right (Real.rpow_le_rpow (by norm_num)
    (by exact_mod_cast prime_norm_ge_two P hp) hδ.le) 1

theorem uniform_primeMass_product (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset (Ideal O), (∀ P ∈ S,Prime P) →
      (∏ P ∈ S,primeMass P δ) ≤ C := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2:ℝ)))
  let small : Finset (Ideal O) := (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset
  let B : ℝ := max 1 (((2:ℝ)^δ-1)⁻¹)
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B^small.card,pow_pos (zero_lt_one.trans_le hB) _,?_⟩
  intro S hp
  have hs (P : Ideal O) (hP : P ∈ S∩small) : primeMass P δ ≤ B :=
    (primeMass_le_fixed P (hp P (Finset.mem_inter.mp hP).1) δ hδ).trans (le_max_right _ _)
  have hl (P : Ideal O) (hP : P ∈ S\small) : primeMass P δ ≤ 1 := by
    have hn : N < Ideal.absNorm P := by
      by_contra hn
      apply (Finset.mem_sdiff.mp hP).2
      simpa only [small,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using le_of_not_gt hn
    have hpow := hN (Ideal.absNorm P) hn.le
    apply inv_le_one_of_one_le₀
    linarith
  have he : S=(S∩small)∪(S\small) := by
    ext P
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hdis : Disjoint (S∩small) (S\small) := Finset.disjoint_left.mpr
    (fun P hP hQ => (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)
  rw [he,Finset.prod_union hdis]
  have hleft : (∏ P ∈ S∩small,primeMass P δ) ≤ B^small.card := by
    calc
      _ ≤ ∏ _P ∈ S∩small,B := Finset.prod_le_prod₀
        (fun P hP => primeMass_nonneg P (hp P (Finset.mem_inter.mp hP).1) δ hδ) hs
      _ = B^(S∩small).card := by simp
      _ ≤ _ := pow_le_pow_right₀ hB (Finset.card_le_card Finset.inter_subset_right)
  have hright : (∏ P ∈ S\small,primeMass P δ) ≤ 1 :=
    Finset.prod_le_one₀ (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ) hl
  exact (mul_le_mul hleft hright (Finset.prod_nonneg
    (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ)) (by positivity)).trans_eq (mul_one _)

theorem local_power_sum (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) (K : ℕ) :
    (∑ n ∈ Finset.range K,((Ideal.absNorm P:ℝ)^(n+1))^(-δ)) ≤ primeMass P δ := by
  let q : ℝ := (Ideal.absNorm P:ℝ)^δ
  have hNP : (1:ℝ)<Ideal.absNorm P := by exact_mod_cast prime_norm_ge_two P hp
  have hq : 1 < q := Real.one_lt_rpow hNP hδ
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hr1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hsum := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).summable.sum_le_tsum
    (Finset.range K) (fun n _ => mul_nonneg hr0 (pow_nonneg hr0 n))
  rw [((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).tsum_eq] at hsum
  have he (n : ℕ) : ((Ideal.absNorm P:ℝ)^(n+1))^(-δ)=q⁻¹*(q⁻¹)^n := by
    rw [← Real.rpow_natCast_mul (by linarith : (0:ℝ)≤Ideal.absNorm P),mul_comm,
      Real.rpow_mul_natCast (by linarith : (0:ℝ)≤Ideal.absNorm P),Real.rpow_neg (by linarith),pow_succ]
    dsimp only [q]
    ring
  simp_rw [he]
  apply hsum.trans_eq
  change q⁻¹*(1-q⁻¹)⁻¹=(q-1)⁻¹
  field_simp

end SevenEighths.CenteredMomentRankin

end

end OAI

end Source401

/- Original source: OAI/NumberTheory/DirichletL/Moments/RankinCount.lean; sha256: 9855ba9a713837837fd3a4ade1e7734b0478f3189448375fc48a6e12738e5283 -/
section Source402
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinCount
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentRankin
local notation "O" => ActualEisensteinCubic.O

def powerCode (R : Finset (Ideal O)) (I : Ideal O) (P : R) : ℕ :=
  (normalizedFactors I).count (P:Ideal O)-1

theorem powerCode_reconstruct (R : Finset (Ideal O)) (I : Ideal O) (hI : I ≠ 0)
    (hR : primeSupport I=R) :
    I=∏ P : R,(P:Ideal O)^(powerCode R I P+1) := by
  have he (P : R) : powerCode R I P+1=(normalizedFactors I).count (P:Ideal O) := by
    have hp : (P:Ideal O) ∈ primeSupport I := hR ▸ P.property
    have hc := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
    dsimp only [powerCode]
    omega
  simp_rw [he]
  calc
    I=(normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
    _=∏ P ∈ (normalizedFactors I).toFinset,P^(normalizedFactors I).count P := Finset.prod_multiset_count _
    _=∏ P : R,(P:Ideal O)^(normalizedFactors I).count (P:Ideal O) := by
      rw [Finset.prod_coe_sort R (fun P : Ideal O => P^(normalizedFactors I).count P)]
      change _=∏ P ∈ R,P^(normalizedFactors I).count P
      rw [← hR]
      rfl

theorem powerCode_injOn (R : Finset (Ideal O)) (S : Finset (Ideal O))
    (hS : ∀ I ∈ S,I ≠ 0) (hR : ∀ I ∈ S,primeSupport I=R) :
    Set.InjOn (powerCode R) S := by
  intro I hI J hJ he
  rw [powerCode_reconstruct R I (hS I hI) (hR I hI),powerCode_reconstruct R J (hS J hJ) (hR J hJ),he]

theorem ideal_mass_eq (R : Finset (Ideal O)) (I : Ideal O) (hI : I ≠ 0)
    (hR : primeSupport I=R) (δ : ℝ) :
    (Ideal.absNorm I:ℝ)^(-δ)=
      ∏ P : R,((Ideal.absNorm (P:Ideal O):ℝ)^(powerCode R I P+1))^(-δ) := by
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)^(-δ))
    (powerCode_reconstruct R I hI hR)
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow] at he
  rw [he]
  exact (Real.finsetProd_rpow _ _ (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _) _).symm

theorem fixed_support_mass (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal O)),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      (∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ)) ≤ C := by
  obtain ⟨C,hC,hprod⟩ := uniform_primeMass_product δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hsupport
  let K : ℕ := S.sup (fun I => Finset.univ.sup (powerCode R I))+1
  let mass : (R → ℕ) → ℝ := fun v => ∏ P : R,((Ideal.absNorm (P:Ideal O):ℝ)^(v P+1))^(-δ)
  have hm (v : R → ℕ) : 0 ≤ mass v := Finset.prod_nonneg
    (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)
  have hsub : S.image (powerCode R) ⊆ Fintype.piFinset (fun _P : R => Finset.range K) := by
    intro v hv
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hv
    apply Fintype.mem_piFinset.mpr
    intro P
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Finset.le_sup (f := powerCode R I) (Finset.mem_univ P)).trans
      (Finset.le_sup (f := fun I => Finset.univ.sup (powerCode R I)) hI))
  calc
    _ = ∑ v ∈ S.image (powerCode R),mass v := by
      rw [Finset.sum_image (powerCode_injOn R S hS hsupport)]
      apply Finset.sum_congr rfl
      intro I hI
      exact ideal_mass_eq R I (hS I hI) (hsupport I hI) δ
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _P : R => Finset.range K),mass v :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hm v)
    _ = ∏ P : R,∑ n ∈ Finset.range K,((Ideal.absNorm (P:Ideal O):ℝ)^(n+1))^(-δ) := by
      exact (Finset.prod_univ_sum (fun _P : R => Finset.range K)
        (fun P n => ((Ideal.absNorm (P:Ideal O):ℝ)^(n+1))^(-δ))).symm
    _ ≤ ∏ P : R,primeMass P δ := Finset.prod_le_prod₀
      (fun _ _ => Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _))
      (fun P _ => local_power_sum P (hR P P.property) δ hδ K)
    _ ≤ C := by
      have he := Finset.prod_coe_sort R (fun P => primeMass P δ)
      rw [he]
      exact hprod R hR

theorem fixed_support_count (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal O)),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^δ := by
  obtain ⟨C,hC,hmass⟩ := fixed_support_mass δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hs X hX hN
  have hterm (I : Ideal O) (hI : I ∈ S) : (1:ℝ) ≤ X^δ*(Ideal.absNorm I:ℝ)^(-δ) := by
    have hn : (0:ℝ)<Ideal.absNorm I := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
    have hr := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hn.le (hN I hI) hδ.le)
      (Real.rpow_nonneg hn.le (-δ))
    simpa only [← Real.rpow_add hn,add_neg_cancel,Real.rpow_zero] using hr
  calc
    _ = ∑ _I ∈ S,(1:ℝ) := by simp
    _ ≤ ∑ I ∈ S,X^δ*(Ideal.absNorm I:ℝ)^(-δ) := Finset.sum_le_sum (fun I hI => hterm I hI)
    _ = X^δ*∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ) := (Finset.mul_sum _ _ _).symm
    _ ≤ X^δ*C := mul_le_mul_of_nonneg_left (hmass R S hR hS hs) (Real.rpow_nonneg hX.le _)
    _ = _ := mul_comm _ _

end SevenEighths.CenteredMomentRankinCount

end

end OAI

end Source402

/- Original source: OAI/NumberTheory/DirichletL/Moments/Primitive.lean; sha256: 195afc93f5452246997e970cb85d474dc2bbeb82bce6686ad34834b4d4a681b6 -/
section Source403
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentPrimitive
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

def primitiveCharacter {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) :
    MulChar (Residue (finitePrimeModulus P)) ℂ :=
  crtCharacter ((Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
    (IdealGaussCRT.quotientProdEquivPi P hcop)) (fun i => actualSextic (P i) (hg i) ^ j i)

theorem primitiveCharacter_apply {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) (x : Residue (finitePrimeModulus P)) :
    primitiveCharacter P hcop hg j x =
      principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) x := rfl

@[simp] theorem primitiveCharacter_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) (x : O) :
    primitiveCharacter P hcop hg j (Ideal.Quotient.mk _ x) =
      finiteSexticRow P hg j x := by
  exact (primitiveCharacter_apply P hcop hg j _).trans
    (principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) x)

theorem primitive_gauss_transform {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) (h : O) :
    residueGauss (finitePrimeModulus P) (finitePrimeModulus_ne_zero P)
      (primitiveCharacter P hcop hg j) (Ideal.Quotient.mk _ h) =
      star (finiteSexticRow P hg j h) * canonicalGaussSum P hcop hg j := by
  let r := finitePrimeModulus P
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue r) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (Residue r) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  simp only [residueGauss, tsum_fintype, primitiveCharacter_apply]
  rw [canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6
    (finitePrimeModulus P) (span_finitePrimeModulus P)]
  exact congrArg (fun z : ℂ => star z * canonicalGaussSum P hcop hg j)
    (principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) h)

lemma sqrt_absNorm (r : O) :
    Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) = ‖eisEmbedding r‖ := by
  rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]

theorem normalized_primitive_gauss_norm_le_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) (h : O) :
    ‖normalizedResidueGauss (finitePrimeModulus P) (finitePrimeModulus_ne_zero P)
      (primitiveCharacter P hcop hg j) (Ideal.Quotient.mk _ h)‖ ≤ 1 := by
  rw [normalizedResidueGauss, primitive_gauss_transform P hcop hg hchar j hj0 hj6,
    sqrt_absNorm, mul_div_assoc]
  change ‖star (finiteSexticRow P hg j h) * canonicalNormalizedGauss P hcop hg j‖ ≤ 1
  rw [norm_mul, norm_star, norm_canonicalNormalizedGauss P hcop hg hchar j hj0 hj6, mul_one]
  exact QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j h

end SevenEighths.CenteredMomentPrimitive
end

end OAI

end Source403

/- Original source: OAI/NumberTheory/DirichletL/Moments/Bridge.lean; sha256: 89b80c801e704ca580c1456c367dc3514f15083b6dbde48333c36b32ff1256fb -/
section Source404
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentBridge
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentFirstPoisson

def productCharacter (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) :
    MulChar (Residue (a * b)) ℂ where
  toFun x := χa ((principalCRT a b hcop x).1) * χb ((principalCRT a b hcop x).2)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul]; ring
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (principalCRT a b hcop x) := fun h =>
      hx ((isUnit_map_iff (principalCRT a b hcop) x).mp h)
    rw [Prod.isUnit_iff] at hn
    by_cases h : IsUnit (principalCRT a b hcop x).1
    · rw [χb.map_nonunit (fun hb => hn ⟨h, hb⟩), mul_zero]
    · rw [χa.map_nonunit h, zero_mul]

theorem productCharacter_apply (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : Residue (a * b)) :
    productCharacter a b hcop χa χb x =
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (frequencyReduction b (a * b) (dvd_mul_left b a) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [productCharacter, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    principalCRT_mk, frequencyReduction_mk]

@[simp] theorem productCharacter_mk (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : O) :
    productCharacter a b hcop χa χb (Ideal.Quotient.mk _ x) =
      χa (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x) := by
  rw [productCharacter_apply, frequencyReduction_mk, frequencyReduction_mk]

theorem productCharacter_gauss (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    residueGauss (a * b) (mul_ne_zero ha hb) (productCharacter a b hcop χa χb) h =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        residueGauss b hb χb (frequencyReduction b (a * b) (dvd_mul_left b a) h) := by
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (mul_ne_zero ha hb)
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  simpa only [residueGauss, tsum_fintype, productCharacter_apply] using
    coprime_character_fourier a b ha hb hcop χa χb h

theorem triple_pair_gauss (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (j : O) :
    residueGauss (r * (a * b)) (mul_ne_zero hr (mul_ne_zero ha hb))
      (productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹))
      (Ideal.Quotient.mk _ j) =
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
  let := finite_quotient_span hb
  rw [productCharacter_gauss r (a * b) hr (mul_ne_zero ha hb),
    frequencyReduction_mk, frequencyReduction_mk,
    productCharacter_mk, productCharacter_gauss a b ha hb, frequencyReduction_mk,
    frequencyReduction_mk, residueGauss_inverse, ← map_neg]
  simp only [map_mul, star_mul, MulChar.star_apply']
  ring

theorem triple_pair_poisson (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
      star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      ∑' j : O, (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
        paperRadialFourier W
          (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  let χ := productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹)
  have hm : r * (a * b) ≠ 0 := mul_ne_zero hr (mul_ne_zero ha hb)
  let := finite_quotient_span hm
  let := finite_quotient_span hb
  let : Fintype (Residue (r * (a * b))) := Fintype.ofFinite _
  have hχ (z : O) : χ (Ideal.Quotient.mk _ z) =
      ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
        star (χb (Ideal.Quotient.mk _ z)) := by
    simp only [χ, productCharacter_mk, MulChar.star_apply', mul_assoc]
  have hp := actual_radial_paper_poisson_trace W K hK (r * (a * b)) hm χ
  change (∑' z : O, χ (Ideal.Quotient.mk _ z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
    (K / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) •
    ∑' j : O, (∑ x : Residue (r * (a * b)),
      χ x * quotientTrace (r * (a * b)) hm (Ideal.Quotient.mk _ j * x)) *
      paperRadialFourier W
        (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) at hp
  simp only [hχ] at hp
  rw [hp]
  have hcoeff (j : O) : (∑ x : Residue (r * (a * b)),
      χ x * quotientTrace (r * (a * b)) hm (Ideal.Quotient.mk _ j * x)) =
      residueGauss (r * (a * b)) hm χ (Ideal.Quotient.mk _ j) := by
    simp only [residueGauss, tsum_fintype]
  simp_rw [hcoeff]
  simp_rw [χ, triple_pair_gauss r a b hr ha hb hrab hab ξ χa χb]
  simp_rw [mul_assoc, tsum_mul_left]
  rw [Complex.real_smul]

theorem masked_triple_pair_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι)
    (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, rowCoprimeMask P S z *
      (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
        star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ∑ E ∈ S.powerset,
        let e := primeSubsetGenerator P E
        let Ke := K / ‖eisEmbedding e‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        (ξ (Ideal.Quotient.mk _ e) * χa (Ideal.Quotient.mk _ e) *
          star (χb (Ideal.Quotient.mk _ e))) *
        ((Ke / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
        (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
          star (χb (Ideal.Quotient.mk _ (r * a)))) *
        ∑' j : O, (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
          residueGauss a ha χa (Ideal.Quotient.mk _ j) *
          star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
          paperRadialFourier W
            (Ke * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  let χ := productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹)
  have hm : r * (a * b) ≠ 0 := mul_ne_zero hr (mul_ne_zero ha hb)
  let := finite_quotient_span hm
  let := finite_quotient_span hb
  let : Fintype (Residue (r * (a * b))) := Fintype.ofFinite _
  let row := fun z : O => ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
    star (χb (Ideal.Quotient.mk _ z))
  have hχ (z : O) : χ (Ideal.Quotient.mk _ z) = row z := by
    simp only [χ, row, productCharacter_mk, MulChar.star_apply', mul_assoc]
  have hsum : Summable (fun z : O => row z * W (‖eisEmbedding z‖ ^ 2 / K)) := by
    have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
      (Ideal.Quotient.mk (Ideal.span {r * (a * b)})) χ
    simpa only [hχ, scaledRadialTest_apply] using hs
  have hmul (x y : O) : row (x * y) = row x * row y := by
    simp only [row, map_mul, star_mul]
    ring
  rw [tsum_masked_radial_dilations P hinj S row hmul W K hsum]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  rw [triple_pair_poisson r a b hr ha hb hrab hab ξ χa χb W
    (K / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)
    (primeSubset_reducedScale_pos P E hK)]
  ring

theorem normalized_triple_pair_poisson
    (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
      star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {b}) : ℝ) : ℂ))) *
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      ∑' j : O, (normalizedResidueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
        paperRadialFourier W
          (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  have hnr : (‖eisEmbedding r‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hr))
  have hna : (‖eisEmbedding a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))
  have hnb : (‖eisEmbedding b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hb))
  have hpoint (j : O) : residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
      residueGauss a ha χa (Ideal.Quotient.mk _ j) *
      star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j))) =
      ((‖eisEmbedding r‖ : ℂ) * (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ)) *
      (normalizedResidueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
    simp only [normalizedResidueGauss, CenteredMomentPrimitive.sqrt_absNorm,
      star_div₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
  rw [triple_pair_poisson r a b hr ha hb hrab hab ξ χa χb W K hK]
  simp_rw [hpoint, mul_assoc, tsum_mul_left, CenteredMomentPrimitive.sqrt_absNorm]
  simp only [map_mul, norm_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul]
  field_simp

end SevenEighths.CenteredMomentBridge
end

end OAI

end Source404

/- Original source: OAI/NumberTheory/DirichletL/Moments/Initial.lean; sha256: 177e295031bce4d28c87389435315cbfc2ef0ffad4b25ddaf7aa9f20189f1be8 -/
section Source405
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentInitial
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentBridge

variable {ι : Type*}

abbrev activeModulus (P : ι → Ideal O) (B : Finset ι) (c d : ι → ℕ) : O :=
  finitePrimeModulus (fun i : CenteredMomentActive.activeSupport B c d => P i.val)

def commonCharacter (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (B : Finset ι) (c d : ι → ℕ) : MulChar (Residue (activeModulus P B c d)) ℂ :=
  primitiveCharacter (fun i : CenteredMomentActive.activeSupport B c d => P i.val)
    (CenteredMomentActive.activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => CenteredMomentActive.netExponent (c i.val) (d i.val))

theorem activeModulus_ne_zero (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (B : Finset ι) (c d : ι → ℕ) : activeModulus P B c d ≠ 0 :=
  finitePrimeModulus_ne_zero _

theorem activeModulus_coprime (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (B : Finset ι) (c d : ι → ℕ) (v : O)
    (hcop : ∀ i ∈ B, IsCoprime (P i) (Ideal.span {v})) :
    IsCoprime (activeModulus P B c d) v := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [activeModulus, span_finitePrimeModulus]
  apply IsCoprime.prod_left
  intro i _
  exact hcop i.val (Finset.mem_filter.mp i.property).1

theorem allocated_pair_factor (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) (z : O) :
    idealRowHom z ((∏ i ∈ B, P i ^ c i) * Ideal.span {a}) *
      star (idealRowHom z ((∏ i ∈ B, P i ^ d i) * Ideal.span {b})) =
      rowCoprimeMask P (CenteredMomentActive.principalSupport B c d) z *
      (commonCharacter P hinj hg B c d (Ideal.Quotient.mk _ z) *
        supportedModulusCharacter a ha (Ideal.Quotient.mk _ z) *
        star (supportedModulusCharacter b hb (Ideal.Quotient.mk _ z))) := by
  calc
    _ = (idealRowHom z (∏ i ∈ B, P i ^ c i) *
        star (idealRowHom z (∏ i ∈ B, P i ^ d i))) *
        (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) := by
      rw [map_mul, map_mul, star_mul]
      ring
    _ = _ := by
      rw [CenteredMomentActive.common_ideal_pair_active P hg hchar B c d hc hd]
      simp only [commonCharacter, primitiveCharacter_mk, supportedModulusCharacter_mk]
      ring

theorem allocated_pair_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hcop : ∀ i ∈ B, IsCoprime (P i) (Ideal.span {a * b})) (hab : IsCoprime a b)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    let r := activeModulus P B c d
    let ξ := commonCharacter P hinj hg B c d
    let χa := supportedModulusCharacter a ha
    let χb := supportedModulusCharacter b hb
    (∑' z : O, (idealRowHom z ((∏ i ∈ B, P i ^ c i) * Ideal.span {a}) *
      star (idealRowHom z ((∏ i ∈ B, P i ^ d i) * Ideal.span {b}))) *
      W (‖eisEmbedding z‖ ^ 2 / K)) =
      ∑ E ∈ (CenteredMomentActive.principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        let Ke := K / ‖eisEmbedding e‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        (ξ (Ideal.Quotient.mk _ e) * χa (Ideal.Quotient.mk _ e) *
          star (χb (Ideal.Quotient.mk _ e))) *
        ((Ke / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
        (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
          star (χb (Ideal.Quotient.mk _ (r * a)))) *
        ∑' j : O, (residueGauss r (activeModulus_ne_zero P B c d) ξ (Ideal.Quotient.mk _ j) *
          residueGauss a (supported_element_ne_zero a ha) χa (Ideal.Quotient.mk _ j) *
          star (residueGauss b (supported_element_ne_zero b hb) χb (Ideal.Quotient.mk _ (-j)))) *
          paperRadialFourier W
            (Ke * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  simp_rw [allocated_pair_factor P hinj hg hchar B c d hc hd a b ha hb]
  exact masked_triple_pair_poisson P hinj (CenteredMomentActive.principalSupport B c d)
    (activeModulus P B c d) a b (activeModulus_ne_zero P B c d)
    (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
    (activeModulus_coprime P B c d (a * b) hcop) hab
    (commonCharacter P hinj hg B c d) (supportedModulusCharacter a ha)
    (supportedModulusCharacter b hb) W K hK

theorem common_gauss_norm_le_one (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ) (h : O) :
    ‖normalizedResidueGauss (activeModulus P B c d) (activeModulus_ne_zero P B c d)
      (commonCharacter P hinj hg B c d) (Ideal.Quotient.mk _ h)‖ ≤ 1 :=
  normalized_primitive_gauss_norm_le_one
    (fun i : CenteredMomentActive.activeSupport B c d => P i.val)
    (CenteredMomentActive.activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => CenteredMomentActive.netExponent (c i.val) (d i.val))
    (CenteredMomentActive.netExponent_ne_zero B c d)
    (fun _i => CenteredMomentActive.netExponent_lt_six _ _) h

end SevenEighths.CenteredMomentInitial
end

end OAI

end Source405

/- Original source: OAI/NumberTheory/DirichletL/Moments/Smooth.lean; sha256: 3ed97ce1f925a280163fe57aa4a0a7092d391ca1235746ee7763308c153a0dd7 -/
section Source406
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.CenteredMomentSmooth
open FourierBridge EisensteinSchwartzPoisson

def rootWindow (V : ℝ → ℂ) (u : ℝ) : ℂ := V u / (Real.sqrt (Real.exp u) : ℂ)

def wholeKernel (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (R ρ x u v : ℝ) : ℂ :=
  V 0 ρ * V 1 x * rootWindow (V 2) u * rootWindow (V 3) v *
    paperRadialFourier W (R * Real.exp (ρ + x - u - v))

def rowPhase (V : Fin 4 → ℝ → ℂ) (ρ x t : ℝ) : ℂ :=
  (V 0 ρ * logPhase t ρ) * (V 1 x * logPhase t x)

def columnPhase (V : ℝ → ℂ) (u t : ℝ) : ℂ :=
  rootWindow V u * logPhase t (-u)

def separatedKernel (V : Fin 4 → ℝ → ℂ) (ρ x u v t : ℝ) : ℂ :=
  rowPhase V ρ x t * columnPhase (V 2) u t * columnPhase (V 3) v t

theorem whole_kernel_separation (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ ρ x u v : ℝ, wholeKernel W V R ρ x u v =
        ∫ t : ℝ, separatedKernel V ρ x u v t * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  let U : Fin 4 → ℝ → ℂ := ![V 0, V 1, rootWindow (V 2), rootWindow (V 3)]
  let a : Fin 4 → ℝ := ![1, 1, -1, -1]
  have hU : ∀ i y, U i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i
    · exact hV 0 y hy
    · exact hV 1 y hy
    · apply hV 2 y
      intro hz
      exact hy (by simp [U, rootWindow, hz])
    · apply hV 3 y
      intro hz
      exact hy (by simp [U, rootWindow, hz])
  obtain ⟨C, hC, hs⟩ := paperRadialFourier_log_separation_envelope W U a M hM hU A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  refine ⟨b, ?_, hi, hm, hp⟩
  intro ρ x u v
  have h := hb ![ρ, x, u, v]
  simpa [U, a, wholeKernel, separatedKernel, rowPhase, columnPhase,
    Fin.prod_univ_succ, Fin.sum_univ_succ, sub_eq_add_neg, mul_assoc, add_assoc] using h

lemma separated_integrable (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (ρ x u v : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ => c * separatedKernel V ρ x u v t * b t) := by
  let K : ℝ := ‖c‖ * ‖V 0 ρ‖ * ‖V 1 x‖ * ‖rootWindow (V 2) u‖ * ‖rootWindow (V 3) v‖
  apply (b.integrable.norm.const_mul K).mono'
  · have hρ := logPhase_continuous_left ρ
    have hx := logPhase_continuous_left x
    have hu := logPhase_continuous_left (-u)
    have hv := logPhase_continuous_left (-v)
    exact (by unfold separatedKernel rowPhase columnPhase; fun_prop : Continuous (fun t : ℝ =>
      c * separatedKernel V ρ x u v t * b t)).aestronglyMeasurable
  · filter_upwards [] with t
    simp only [separatedKernel, rowPhase, columnPhase, norm_mul, logPhase_norm, mul_one]
    dsimp only [K]
    ring_nf
    exact le_rfl

theorem finite_pair_separation {α β : Type*}
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (R : ℝ) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ ρ x u v : ℝ, wholeKernel W V R ρ x u v =
      ∫ t : ℝ, separatedKernel V ρ x u v t * b t)
    (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (ρ x : ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, (c i * star (d j)) * wholeKernel W V R ρ x (u i) (v j)) =
      ∫ t : ℝ, rowPhase V ρ x t *
        (∑ i ∈ S, c i * columnPhase (V 2) (u i) t) *
        (∑ j ∈ T, star (d j) * columnPhase (V 3) (v j) t) * b t := by
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∫ t : ℝ,
        (c i * star (d j)) * separatedKernel V ρ x (u i) (v j) t * b t := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsep, ← integral_const_mul]
      congr 1
      funext t
      ring
    _ = ∫ t : ℝ, ∑ i ∈ S, ∑ j ∈ T,
        (c i * star (d j)) * separatedKernel V ρ x (u i) (v j) t * b t := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum T
        (fun j _ => separated_integrable b V ρ x (u i) (v j) (c i * star (d j))))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ =>
        separated_integrable b V ρ x (u i) (v j) (c i * star (d j)))]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [Finset.sum_mul, Finset.mul_sum, separatedKernel]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem whole_product_pair_separation (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ {α β : Type*} (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
        (u : α → ℝ) (v : β → ℝ) (ρ x : ℝ),
        (∑ i ∈ S, ∑ j ∈ T, (c i * star (d j)) * wholeKernel W V R ρ x (u i) (v j)) =
          ∫ t : ℝ, rowPhase V ρ x t *
            (∑ i ∈ S, c i * columnPhase (V 2) (u i) t) *
            (∑ j ∈ T, star (d j) * columnPhase (V 3) (v j) t) * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨C, hC, hs⟩ := whole_kernel_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  exact ⟨b, fun S T c d u v ρ x => finite_pair_separation W V R b hb S T c d u v ρ x,
    hi, hm, hp⟩

theorem logPhase_norm_ratio (q X θ : ℝ) (hq : 0 < q) (hX : 0 < X) :
    logPhase θ (-Real.log (q / X)) =
      logPhase θ (Real.log X) * (q : ℂ) ^ (Complex.I * (-(2 * Real.pi * θ))) := by
  have hlog : -Real.log (q / X) = Real.log X + -Real.log q := by
    rw [Real.log_div hq.ne' hX.ne']
    ring
  rw [hlog, logPhase_add]
  congr 1
  have hθ : (-(2 * Real.pi * θ)) / (2 * Real.pi) = -θ := by
    have hp := Real.pi_ne_zero
    field_simp
  have hn := CenteredMomentLattice.logPhase_eq_normPower (-(2 * Real.pi * θ)) q hq
  rw [hθ] at hn
  push_cast at hn
  rw [← hn]
  unfold logPhase
  congr 1
  push_cast
  ring

open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

theorem idealWeight_height_add (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R I : Ideal O) (hI : I ≠ 0) (t v : ℝ) :
    idealWeight c χ R (t + v) I =
      idealWeight c χ R t I * (Ideal.absNorm I : ℂ) ^ (Complex.I * v) := by
  have hn : (Ideal.absNorm I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [idealWeight, Complex.ofReal_add, mul_add, Complex.cpow_add _ _ hn]
  ring

theorem idealWeight_whole_phase (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R I : Ideal O) (hI : I ≠ 0) (t θ X : ℝ) (hX : 0 < X) :
    idealWeight c χ R t I * logPhase θ (-Real.log ((Ideal.absNorm I : ℝ) / X)) =
      logPhase θ (Real.log X) * idealWeight c χ R (t - 2 * Real.pi * θ) I := by
  have hn : (0 : ℝ) < Ideal.absNorm I := by
    exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  rw [logPhase_norm_ratio _ X θ hn hX, sub_eq_add_neg, idealWeight_height_add c χ R I hI]
  push_cast
  ring

theorem centered_whole_phase (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R Qslot I J : Ideal O) (hQslot : Qslot ≠ 0) (hI : I ≠ 0) (hJ : J ≠ 0)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ t θ X : ℝ) (hX : 0 < X) :
    (idealWeight c χ R t (Qslot * I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) *
      logPhase θ (-Real.log ((Ideal.absNorm (Qslot * I * J) : ℝ) / X)) =
      logPhase θ (Real.log X) *
        (idealWeight c χ R (t - 2 * Real.pi * θ) (Qslot * I * J) *
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) := by
  calc
    _ = (idealWeight c χ R t (Qslot * I * J) *
        logPhase θ (-Real.log ((Ideal.absNorm (Qslot * I * J) : ℝ) / X))) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J := by ring
    _ = _ := by
      rw [idealWeight_whole_phase c χ R (Qslot * I * J) (mul_ne_zero (mul_ne_zero hQslot hI) hJ) t θ X hX]
      ring

end SevenEighths.CenteredMomentSmooth
end

end OAI

end Source406

/- Original source: OAI/NumberTheory/DirichletL/Moments/Cauchy.lean; sha256: 8383bc0e47dacb25f88a86b6f843db6b43c9f175a89f635f268f416c2819eba9 -/
section Source407
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.CenteredMomentCauchy
open CenteredMomentSmooth FourierBridge

theorem bounded_row_cauchy {κ : Type*} (rows : Finset κ)
    (w A B : κ → ℂ) (hw : ∀ k ∈ rows, ‖w k‖ ≤ 1) :
    ‖∑ k ∈ rows, w k * A k * B k‖ ≤
      Real.sqrt (∑ k ∈ rows, ‖A k‖ ^ 2) * Real.sqrt (∑ k ∈ rows, ‖B k‖ ^ 2) := by
  calc
    _ ≤ ∑ k ∈ rows, ‖w k * A k * B k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ rows, ‖A k‖ * ‖B k‖ := Finset.sum_le_sum fun k hk => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg _) (hw k hk)) (norm_nonneg _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt rows _ _

def leftColumn {α : Type*} (S : Finset α) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, c i * columnPhase V (u i) t

def rightColumn {β : Type*} (T : Finset β) (d : β → ℂ)
    (V : ℝ → ℂ) (v : β → ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ T, star (d j) * columnPhase V (v j) t

lemma paired_columns_integrable {α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (ρ x : ℝ)
    (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (z : ℂ) :
    Integrable (fun t : ℝ => z * (rowPhase V ρ x t *
      leftColumn S c (V 2) u t * rightColumn T d (V 3) v t * b t)) := by
  have hi := integrable_finsetSum S (fun i _ => integrable_finsetSum T
    (fun j _ => separated_integrable b V ρ x (u i) (v j) (z * c i * star (d j))))
  convert hi using 1
  funext t
  simp only [leftColumn, rightColumn, Finset.mul_sum, Finset.sum_mul, separatedKernel]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem common_density_cauchy {κ α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (rows : Finset κ) (S : Finset α) (T : Finset β)
    (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
    (ρ x : κ → ℝ) (η : κ → ℂ)
    (hη : ∀ k ∈ rows, ‖η k‖ ≤ 1)
    (hV₀ : ∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) (hV₁ : ∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1)
    (E : ℝ) (_hE : 0 ≤ E) (J : ℕ)
    (henergy : ∀ t : ℝ,
      Real.sqrt (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ ^ 2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn T (d k) (V 3) v t‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) :
    ‖∑ k ∈ rows, η k * ∫ t : ℝ, rowPhase V (ρ k) (x k) t *
      leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t‖ ≤
      E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
  have hrow (k : κ) (hk : k ∈ rows) (t : ℝ) : ‖η k * rowPhase V (ρ k) (x k) t‖ ≤ 1 := by
    rw [norm_mul, rowPhase, norm_mul, norm_mul, norm_mul, logPhase_norm, logPhase_norm, mul_one, mul_one]
    exact (mul_le_of_le_one_left (by positivity) (hη k hk)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hV₀ k hk)).trans (hV₁ k hk))
  have hpoint (t : ℝ) :
      ‖∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ ≤
        E * ((1 + ‖t‖) ^ J * ‖b t‖) := by
    have hs := bounded_row_cauchy rows (fun k => η k * rowPhase V (ρ k) (x k) t)
      (fun k => leftColumn S (c k) (V 2) u t) (fun k => rightColumn T (d k) (V 3) v t)
      (fun k hk => hrow k hk t)
    have he : (∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)) =
        (∑ k ∈ rows, (η k * rowPhase V (ρ k) (x k) t) *
          leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t) * b t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hs.trans (henergy t)) (norm_nonneg _)).trans_eq (by ring)
  have hi : Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) :=
    JointLogSeparation.weighted_schwartz_integrable b J
  calc
    _ = ‖∫ t : ℝ, ∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ := by
      congr 1
      rw [integral_finsetSum _ (fun k _ =>
        paired_columns_integrable b V (ρ k) (x k) S T (c k) (d k) u v (η k))]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul]
    _ ≤ ∫ t : ℝ, E * ((1 + ‖t‖) ^ J * ‖b t‖) :=
      norm_integral_le_of_norm_le (hi.const_mul E) (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

theorem whole_kernel_row_estimate (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {κ α β : Type*} (rows : Finset κ) (S : Finset α) (T : Finset β)
        (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : κ → ℝ) (η : κ → ℂ),
      (∀ k ∈ rows, ‖η k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ, Real.sqrt (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ ^ 2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn T (d k) (V 3) v t‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) →
      (1 + R) ^ A * ‖∑ k ∈ rows, η k *
        (∑ i ∈ S, ∑ j ∈ T, (c k i * star (d k j)) *
          wholeKernel W V R (ρ k) (x k) (u i) (v j))‖ ≤ C * E := by
  obtain ⟨C, hC, hs⟩ := whole_product_pair_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR κ α β rows S T c d u v ρ x η hη hV₀ hV₁ E hE he
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  have hid (k : κ) := hb S T (c k) (d k) u v (ρ k) (x k)
  simp_rw [hid]
  have hcs := common_density_cauchy b V rows S T c d u v ρ x η hη hV₀ hV₁ E hE J he
  change (1 + R) ^ A * ‖∑ k ∈ rows, η k * ∫ t : ℝ,
    rowPhase V (ρ k) (x k) t * leftColumn S (c k) (V 2) u t *
      rightColumn T (d k) (V 3) v t * b t‖ ≤ _
  calc
    _ ≤ (1 + R) ^ A * (E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = E * ((1 + R) ^ A * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ ≤ E * C := mul_le_mul_of_nonneg_left hm hE
    _ = _ := mul_comm _ _

end SevenEighths.CenteredMomentCauchy
end

end OAI

end Source407

/- Original source: OAI/NumberTheory/DirichletL/Moments/RowNorm.lean; sha256: ffd74c13888b96610cba8b7152f2d5e92c5715e2a4b3ee37192ea9ca10787aed -/
section Source408
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRowNorm
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

def pairResidue (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x : Residue (a * b)) : ℂ :=
  supportedModulusCharacter a ha (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (supportedModulusCharacter b hb
      (frequencyReduction b (a * b) (dvd_mul_left b a) x))

@[simp] theorem pairResidue_mk (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (z : O) :
    pairResidue a b ha hb (Ideal.Quotient.mk _ z) =
      idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b})) := by
  simp only [pairResidue, frequencyReduction_mk, supportedModulusCharacter_mk]

def pairFourier (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (h : O) : ℂ :=
  ∑' x : Residue (a * b), pairResidue a b ha hb x *
    quotientTrace (a * b) (mul_ne_zero (supported_element_ne_zero a ha)
      (supported_element_ne_zero b hb)) (Ideal.Quotient.mk _ h * x)

theorem row_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O =>
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  have h := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) (pairResidue a b ha hb)
  simpa only [pairResidue_mk, scaledRadialTest_apply] using h

theorem row_pair_poisson (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O,
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖eisEmbedding z‖ ^ 2 / K)) =
    ((K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) : ℂ) *
      ∑' h : O, pairFourier a b ha hb h *
        paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (a * b)‖ ^ 2) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  have h := actual_radial_paper_poisson_trace W K hK (a * b)
    (mul_ne_zero (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))
    (pairResidue a b ha hb)
  simpa only [pairResidue_mk, pairFourier, quotientTrace, tsum_fintype, Complex.real_smul] using h

def rowPolynomial {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ) (z : O) : ℂ :=
  ∑ i ∈ S, c i * idealRowHom z (Ideal.span {a i})

def rowEnergy {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O, ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖eisEmbedding z‖ ^ 2 / K)

theorem rowPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ) (z : O) :
    ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (idealRowHom z (Ideal.span {a i}) * star (idealRowHom z (Ideal.span {a j}))) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [rowPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem rowEnergy_expand {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    rowEnergy S a c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : O, (idealRowHom z (Ideal.span {a i}) *
          star (idealRowHom z (Ideal.span {a j}))) * W (‖eisEmbedding z‖ ^ 2 / K) := by
  have hs (i j : α) := (row_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [rowEnergy, rowPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)).summable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  simp only [tsum_mul_left]

theorem rowEnergy_poisson {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    rowEnergy S a c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (((K / ‖eisEmbedding (a i * a j)‖ ^ 2 : ℝ) : ℂ) *
          ∑' h : O, pairFourier (a i) (a j) (ha i) (ha j) h *
            paperRadialFourier W
              (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (a i * a j)‖ ^ 2)) := by
  rw [rowEnergy_expand S a c ha W K hK]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [row_pair_poisson (a i) (a j) (ha i) (ha j) W K hK]

end SevenEighths.CenteredMomentRowNorm

end

end OAI

end Source408

/- Original source: OAI/NumberTheory/DirichletL/Moments/GaussEnergy.lean; sha256: e91c9f7a2ae35f14ce944534e8e2977833a023dc316f6e59c00a0b5d97a3b10e -/
section Source409
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentGaussEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CenteredMomentFourier CenteredMomentPoisson
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def gaussRow (a : O) (ha : Supported (Ideal.span {a})) (z : O) : ℂ :=
  ProbePhysical.sexticGauss a (supported_element_ne_zero a ha) z /
    (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)

theorem gaussRow_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => gaussRow a ha z * star (gaussRow b hb z) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  let P : Residue (a * b) → ℂ := fun x =>
    normalizedResidueGauss a (supported_element_ne_zero a ha)
      (supportedModulusCharacter a ha) (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (normalizedResidueGauss b (supported_element_ne_zero b hb)
      (supportedModulusCharacter b hb) (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) P
  simpa only [P, frequencyReduction_mk, normalizedResidueGauss,
    residueGauss_supported_mk, scaledRadialTest_apply, gaussRow] using hs

def gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (z : O) : ℂ :=
  ∑ i ∈ S, c i * gaussRow (a i) (ha i) z

def gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O, ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖eisEmbedding z‖ ^ 2 / K)

theorem gaussPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (z : O) :
    ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [gaussPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gaussEnergy_expand {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    gaussEnergy S a ha c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : O, (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) *
          W (‖eisEmbedding z‖ ^ 2 / K) := by
  have hs (i j : α) := (gaussRow_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [gaussEnergy, gaussPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)).summable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  simp only [tsum_mul_left]

theorem gaussEnergy_summable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  have hs (i j : α) := (gaussRow_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [gaussPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  exact (hasSum_sum (fun i _ =>
    (hasSum_sum (fun j _ => (hs i j).hasSum)))).summable

theorem finite_energy_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2) ≤
      (gaussEnergy S a ha c W K).re := by
  have hs := Complex.hasSum_re (gaussEnergy_summable S a ha c W K hK).hasSum
  change HasSum _ (gaussEnergy S a ha c W K).re at hs
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hs
  calc
    _ ≤ ∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2 *
        (W (‖eisEmbedding z‖ ^ 2 / K)).re := by
      apply Finset.sum_le_sum
      intro z hz
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z)) hs

theorem gaussEnergy_poisson {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    gaussEnergy S a ha c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ) *
          (Real.sqrt (Ideal.absNorm (Ideal.span {a j}) : ℝ) : ℂ))) *
          ∑' h : O, actualCorrelation (a i) (a j) (ha i) (ha j) (-h) *
            paperRadialFourier W
              (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (a i * a j)‖ ^ 2)) := by
  rw [gaussEnergy_expand S a ha c W K hK]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [gaussRow]
  rw [sextic_gauss_pair_poisson (a i) (a j) (ha i) (ha j) W K hK]

end SevenEighths.CenteredMomentGaussEnergy

end

end OAI

end Source409

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondDiagonal.lean; sha256: bf84acd6f2501049af78b952def37a0e69a11f4adde76a136a7dafa60ac63c67 -/
section Source410
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondDiagonal
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem full_zero_off_diagonal (u v : O)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χ : MulChar (Residue u) ℂ) (ψ : MulChar (Residue v) ℂ)
    (hne : (Ideal.span {u} : Ideal O) ≠ Ideal.span {v}) :
    fullModulusCorrelation u v χ ψ 0 = 0 := by
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_congruence]
  split_ifs with hc
  · by_cases hx0 : χ (Ideal.Quotient.mk _ x) = 0
    · rw [hx0,zero_mul]
    by_cases hy0 : ψ (Ideal.Quotient.mk _ y) = 0
    · rw [hy0,star_zero,mul_zero]
    have hux : IsCoprime u x := ((Ideal.isCoprime_span_singleton_iff x u).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hx0))).symm
    have hvy : IsCoprime v y := ((Ideal.isCoprime_span_singleton_iff y v).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hy0))).symm
    simp only [sub_zero] at hc
    have hu : u ∣ v*x := by
      have he := dvd_add ((dvd_mul_right u v).trans hc) (dvd_mul_right u y)
      convert he using 1 ; ring
    have hv : v ∣ u*y := by
      have he := dvd_sub (dvd_mul_right v x) ((dvd_mul_left v u).trans hc)
      convert he using 1 ; ring
    have huv := hux.dvd_of_dvd_mul_right hu
    have hvu := hvy.dvd_of_dvd_mul_right hv
    exact False.elim (hne (le_antisymm (Ideal.span_singleton_le_span_singleton.mpr hvu)
      (Ideal.span_singleton_le_span_singleton.mpr huv)))
  · rfl

theorem full_same_zero (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    fullModulusCorrelation u u χ χ 0 = ∑ x : Residue u, χ x*star (χ x) := by
  have hcong (x y : Residue u) :
      scaledResidue u u (u*u) rfl x - scaledResidue u u (u*u) (mul_comm u u) y =
        Ideal.Quotient.mk (Ideal.span {u*u}) 0 ↔ x=y := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [scaledResidue_congruence,sub_zero,← mul_sub,mul_dvd_mul_iff_left hu]
    exact Ideal.mem_span_singleton.symm.trans Ideal.Quotient.eq.symm
  simp only [fullModulusCorrelation,fullCorrelation,hcong,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem full_same_zero_norm_le (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    ‖fullModulusCorrelation u u χ χ 0‖ ≤ (Fintype.card (Residue u) : ℝ) := by
  rw [full_same_zero u hu χ]
  calc
    _ ≤ ∑ x : Residue u, ‖χ x*star (χ x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hn : χ x = 0
      · simp only [hn,zero_mul,norm_zero,zero_le_one]
      · rw [MulChar.star_apply',MulChar.inv_apply_eq_inv',mul_inv_cancel₀ hn,norm_one]
    _ = _ := by simp

theorem actual_zero_off_diagonal (u v : O) (hu : Supported (Ideal.span {u}))
    (hv : Supported (Ideal.span {v}))
    (hpu : ConcretePrimeRowBridge.goodLambda^2 ∣ u-1)
    (hpv : ConcretePrimeRowBridge.goodLambda^2 ∣ v-1) (hne : u ≠ v) :
    actualCorrelation u v hu hv 0 = 0 := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  apply full_zero_off_diagonal u v
  intro he
  apply hne
  rw [← primaryGenerator_span u (supported_element_ne_zero u hu) hpu,
    ← primaryGenerator_span v (supported_element_ne_zero v hv) hpv,he]

theorem actual_same_zero_norm_le (u : O) (hu : Supported (Ideal.span {u})) :
    ‖actualCorrelation u u hu hu 0‖ ≤ (Ideal.absNorm (Ideal.span {u}) : ℝ) := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  let : Fintype (Residue u) := Fintype.ofFinite _
  have hb := full_same_zero_norm_le u (supported_element_ne_zero u hu) (supportedModulusCharacter u hu)
  simpa only [actualCorrelation,supportedCorrelation,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hb

theorem divisible_ideal_card (S : Finset (Ideal O)) (s : Ideal O) (hs : s ≠ 0)
    (hS : ∀ I ∈ S, I ≠ 0) (hdiv : ∀ I ∈ S, s ∣ I)
    (Y : ℝ) (hY : 0 ≤ Y) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y/(Ideal.absNorm s : ℝ) := by
  by_cases hempty : S.Nonempty
  · have hquot (I : Ideal O) (hI : I ∈ S) : idealQuotient s I ≠ 0 :=
      ne_zero_of_dvd_ne_zero (hS I hI) (idealQuotient_dvd (hdiv I hI))
    have hbound (I : Ideal O) (hI : I ∈ S) := idealQuotient_norm_le hs (hdiv I hI) Y (hN I hI)
    obtain ⟨I,hI⟩ := hempty
    have hscale : 1 ≤ Y/(Ideal.absNorm s : ℝ) := by
      have hn : (1:ℝ) ≤ Ideal.absNorm (idealQuotient s I) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hquot I hI))
      exact hn.trans (hbound I hI)
    have hc := DescentFiberCost.finite_ideal_count_real (S.image (idealQuotient s)) _ hscale
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hquot I hI)
      (by intro J hJ; obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ; exact hbound I hI)
    rw [Finset.card_image_of_injOn (fun I hI J hJ he => idealQuotient_injective_on s
      (hdiv I hI) (hdiv J hJ) he)] at hc
    convert hc using 1 ; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.card_empty,Nat.cast_zero]
    positivity

def secondZeroEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) : ℂ :=
  ∑ i ∈ S, ∑ j ∈ S, (c i*star (c j)) *
    (actualCorrelation (a i) (a j) (ha i) (ha j) 0 /
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a j}) : ℝ) : ℂ)))

theorem secondZeroEnergy_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) :
    ‖secondZeroEnergy S a ha c‖ ≤ ∑ i ∈ S, ‖c i‖^2 := by
  have hroot (i : α) :
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)) =
        (Ideal.absNorm (Ideal.span {a i}) : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _),Complex.ofReal_natCast]
  have he : secondZeroEnergy S a ha c =
      ∑ i ∈ S, (c i*star (c i)) *
        (actualCorrelation (a i) (a i) (ha i) (ha i) 0 /(Ideal.absNorm (Ideal.span {a i}) : ℂ)) := by
    unfold secondZeroEnergy
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [hroot]
    · intro j hj hji
      have hne : a i ≠ a j := fun he => hji (hinj hi hj he).symm
      rw [actual_zero_off_diagonal _ _ (ha i) (ha j) (hp i) (hp j) hne,zero_div,mul_zero]
    · exact fun hnot => False.elim (hnot hi)
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,norm_mul,norm_star,norm_div,Complex.norm_natCast,← pow_two]
  have hN : 0 < (Ideal.absNorm (Ideal.span {a i}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (ha i).1)
  exact mul_le_of_le_one_right (sq_nonneg _) ((div_le_one hN).mpr (actual_same_zero_norm_le _ (ha i)))

theorem primary_column_card {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y) :
    (S.card : ℝ) ≤ 128*Y/(Ideal.absNorm s : ℝ) := by
  have hspan : Set.InjOn (fun i => (Ideal.span {a i} : Ideal O)) S := by
    intro i hi j hj he
    dsimp only at he
    apply hinj hi hj
    rw [← primaryGenerator_span (a i) (supported_element_ne_zero _ (ha i)) (hp i),
      ← primaryGenerator_span (a j) (supported_element_ne_zero _ (ha j)) (hp j),he]
  have hb := divisible_ideal_card (S.image (fun i => Ideal.span {a i})) s hs
    (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact (ha i).1)
    (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact hdiv i hi)
    Y hY (by intro I hI; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI; exact hN i hi)
  rwa [Finset.card_image_of_injOn hspan] at hb

theorem secondZeroEnergy_divisor_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) (B : ℝ) (_hB : 0 ≤ B)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ B) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y) :
    ‖secondZeroEnergy S a ha c‖ ≤ 128*B^2*Y/(Ideal.absNorm s : ℝ) := by
  calc
    _ ≤ ∑ i ∈ S, ‖c i‖^2 := secondZeroEnergy_bound S a ha hp hinj c
    _ ≤ ∑ _i ∈ S, B^2 := Finset.sum_le_sum (fun i hi =>
      pow_le_pow_left₀ (norm_nonneg _) (hc i hi) 2)
    _ = B^2*(S.card : ℝ) := by simp [mul_comm]
    _ ≤ B^2*(128*Y/(Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left (primary_column_card S a ha hp hinj s hs hdiv Y hY hN) (sq_nonneg _)
    _ = _ := by ring

theorem normalized_secondZeroEnergy_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ B) (s : Ideal O) (hs : s ≠ 0)
    (hdiv : ∀ i ∈ S, s ∣ Ideal.span {a i}) (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ i ∈ S, (Ideal.absNorm (Ideal.span {a i}) : ℝ) ≤ Y)
    (κ : ℂ) (T : ℝ) (hT : 0 < T) :
    ‖(κ/(T:ℂ))*secondZeroEnergy S a ha c‖ ≤
      128*‖κ‖*B^2*Y/(T*(Ideal.absNorm s : ℝ)) := by
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  calc
    _ ≤ (‖κ‖/T)*(128*B^2*Y/(Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (secondZeroEnergy_divisor_bound S a ha hp hinj c B hB hc s hs hdiv Y hY hN)
        (div_nonneg (norm_nonneg _) hT.le)
    _ = _ := by ring

end SevenEighths.CenteredMomentSecondDiagonal

end

end OAI

end Source410

/- Original source: OAI/NumberTheory/DirichletL/Moments/RankinRadical.lean; sha256: 5a2df3014c500ba0d83e89914fa83d1ccbd6df9572f721137ae2979288a00761 -/
section Source411
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinRadical
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O

def commonRadical (I J : Ideal O) : Ideal O :=
  ∏ P ∈ primeSupport I ∩ primeSupport J,P

theorem commonRadical_ne_zero (I J : Ideal O) : commonRadical I J ≠ 0 :=
  support_product_ne_zero Finset.inter_subset_left

theorem commonRadical_squarefree (I J : Ideal O) : Squarefree (commonRadical I J) :=
  squarefree_support_product Finset.inter_subset_left

theorem commonRadical_support (I J : Ideal O) :
    primeSupport (commonRadical I J)=primeSupport I∩primeSupport J := by
  unfold primeSupport commonRadical
  rw [factors_support_product Finset.inter_subset_left]
  simp [primeSupport]

theorem old_mask_dvd_commonRadical (s I J : Ideal O) (hs : Squarefree s)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hsI : s ∣ I) (hsJ : s ∣ J) :
    s ∣ commonRadical I J := by
  apply (squarefree_dvd_iff s _ hs).mpr
  intro P hP
  have hp := support_prime hP
  have hd := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  have hi : P ∈ primeSupport I := by
    simpa only [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hI,hp,true_and]
      using hd.trans hsI
  have hj : P ∈ primeSupport J := by
    simpa only [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hJ,hp,true_and]
      using hd.trans hsJ
  exact Finset.dvd_prod_of_mem id (Finset.mem_inter.mpr ⟨hi,hj⟩)

theorem old_mask_radical_count {α : Type*} (S : Finset α) (I J : α → Ideal O)
    (s : Ideal O) (hs : Squarefree s) (hs0 : s ≠ 0)
    (hI : ∀ a ∈ S,I a ≠ 0) (hJ : ∀ a ∈ S,J a ≠ 0)
    (hsi : ∀ a ∈ S,s ∣ I a) (hsj : ∀ a ∈ S,s ∣ J a)
    (Y : ℝ) (hY : 0 ≤ Y)
    (hN : ∀ a ∈ S,(Ideal.absNorm (commonRadical (I a) (J a)):ℝ) ≤ Y) :
    ((S.image (fun a => commonRadical (I a) (J a))).card:ℝ) ≤
      128*Y/(Ideal.absNorm s:ℝ) := by
  refine CenteredMomentSecondDiagonal.divisible_ideal_card _ s hs0 ?_ ?_ Y hY ?_
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact commonRadical_ne_zero _ _
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact old_mask_dvd_commonRadical s _ _ hs (hI a ha) (hJ a ha) (hsi a ha) (hsj a ha)
  · intro R hR
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hR
    exact hN a ha

end SevenEighths.CenteredMomentRankinRadical

end

end OAI

end Source411

/- Original source: OAI/NumberTheory/DirichletL/Moments/CompleteCommon.lean; sha256: efcfd09aba0b9c2bd96512218cb900f821f5ae62f51c14defa2640c1f62b8dfc -/
section Source412
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCompleteCommon
open UniqueFactorizationMonoid IdealMobiusDivisorSum CenteredMomentSupport
open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def commonSupport (I J : Ideal O) : Finset (Ideal O) := primeSupport I ∩ primeSupport J

def commonPart (I J : Ideal O) : Ideal O :=
  ∏ P ∈ commonSupport I J, P ^ valuation I P

def residualPart (I J : Ideal O) : Ideal O :=
  ∏ P ∈ primeSupport I \ primeSupport J, P ^ valuation I P

theorem commonSupport_comm (I J : Ideal O) : commonSupport I J = commonSupport J I :=
  Finset.inter_comm _ _

theorem supportExtract_eq_power_product (I : Ideal O) (S : Finset (Ideal O)) :
    supportExtract I S = ∏ P ∈ primeSupport I ∩ S, P ^ valuation I P := by
  unfold supportExtract
  rw [Finset.prod_multiset_count_of_subset _ (primeSupport I ∩ S) (by
    intro P hP
    exact Finset.mem_inter.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).1, (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).2⟩)]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [Multiset.count_filter, (Finset.mem_inter.mp hP).2, ↓reduceIte]
  rfl

theorem supportResidual_eq_power_product (I : Ideal O) (S : Finset (Ideal O)) :
    supportResidual I S = ∏ P ∈ primeSupport I \ S, P ^ valuation I P := by
  unfold supportResidual
  rw [Finset.prod_multiset_count_of_subset _ (primeSupport I \ S) (by
    intro P hP
    exact Finset.mem_sdiff.mpr ⟨Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).1, (Multiset.mem_filter.mp
      (Multiset.mem_toFinset.mp hP)).2⟩)]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [Multiset.count_filter, (Finset.mem_sdiff.mp hP).2]
  rfl

theorem commonPart_eq_supportExtract (I J : Ideal O) :
    commonPart I J = supportExtract I (commonSupport I J) := by
  rw [supportExtract_eq_power_product]
  simp only [commonPart, commonSupport, ← Finset.inter_assoc, Finset.inter_self]

theorem residualPart_eq_supportResidual (I J : Ideal O) :
    residualPart I J = supportResidual I (commonSupport I J) := by
  rw [supportResidual_eq_power_product]
  have he : primeSupport I \ commonSupport I J = primeSupport I \ primeSupport J := by
    ext P
    simp only [Finset.mem_sdiff, commonSupport, Finset.mem_inter]
    tauto
  rw [he]
  rfl

theorem commonPart_ne_zero (I J : Ideal O) : commonPart I J ≠ 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_ne_zero _ _

theorem residualPart_ne_zero (I J : Ideal O) : residualPart I J ≠ 0 := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_ne_zero _ _

theorem reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    I = commonPart I J * residualPart I J := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact (support_reconstruct I hI _).symm

theorem commonPart_support (I J : Ideal O) :
    primeSupport (commonPart I J) = commonSupport I J := by
  rw [commonPart_eq_supportExtract, supportExtract_support]
  simp only [commonSupport, ← Finset.inter_assoc, Finset.inter_self]

theorem commonParts_equal_support (I J : Ideal O) :
    primeSupport (commonPart I J) = primeSupport (commonPart J I) := by
  rw [commonPart_support, commonPart_support, commonSupport_comm I J]

theorem residualPart_support (I J : Ideal O) :
    primeSupport (residualPart I J) = primeSupport I \ primeSupport J := by
  rw [residualPart_eq_supportResidual, supportResidual_support]
  ext P
  simp only [Finset.mem_sdiff, commonSupport, Finset.mem_inter]
  tauto

theorem commonPart_valuation (I J P : Ideal O) :
    valuation (commonPart I J) P = if P ∈ commonSupport I J then valuation I P else 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_count I P _

theorem residualPart_valuation (I J P : Ideal O) :
    valuation (residualPart I J) P = if P ∈ commonSupport I J then 0 else valuation I P := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_count I P _

theorem commonPart_residualPart_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J) (residualPart J I) := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual, ← commonSupport_comm I J]
  exact extracted_residual_coprime I J _

theorem commonPart_own_residual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J) (residualPart I J) := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact extracted_residual_coprime I I _

theorem commonProduct_leftResidual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J * commonPart J I) (residualPart I J) :=
  (commonPart_own_residual_coprime I J).mul_left (commonPart_residualPart_coprime J I)

theorem commonProduct_rightResidual_coprime (I J : Ideal O) :
    IsCoprime (commonPart I J * commonPart J I) (residualPart J I) :=
  (commonPart_residualPart_coprime I J).mul_left (commonPart_own_residual_coprime J I)

theorem residualParts_coprime (I J : Ideal O) :
    IsCoprime (residualPart I J) (residualPart J I) := by
  rw [residualPart_eq_supportResidual, residualPart_eq_supportResidual, ← commonSupport_comm I J]
  exact common_support_residual_coprime I J

theorem canonical_complete_extraction (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    I = commonPart I J * residualPart I J ∧
    J = commonPart J I * residualPart J I ∧
    commonPart I J ≠ 0 ∧ commonPart J I ≠ 0 ∧
    residualPart I J ≠ 0 ∧ residualPart J I ≠ 0 ∧
    primeSupport (commonPart I J) = commonSupport I J ∧
    primeSupport (commonPart J I) = commonSupport I J ∧
    primeSupport (residualPart I J) = primeSupport I \ primeSupport J ∧
    primeSupport (residualPart J I) = primeSupport J \ primeSupport I ∧
    IsCoprime (commonPart I J * commonPart J I) (residualPart I J) ∧
    IsCoprime (commonPart I J * commonPart J I) (residualPart J I) ∧
    IsCoprime (residualPart I J) (residualPart J I) := by
  exact ⟨reconstruct I J hI, reconstruct J I hJ,
    commonPart_ne_zero I J, commonPart_ne_zero J I,
    residualPart_ne_zero I J, residualPart_ne_zero J I,
    commonPart_support I J, (commonPart_support J I).trans (commonSupport_comm J I),
    residualPart_support I J, residualPart_support J I,
    commonProduct_leftResidual_coprime I J, commonProduct_rightResidual_coprime I J,
    residualParts_coprime I J⟩

theorem commonPart_dvd (I J : Ideal O) (hI : I ≠ 0) : commonPart I J ∣ I :=
  ⟨residualPart I J, reconstruct I J hI⟩

theorem residualPart_dvd (I J : Ideal O) (hI : I ≠ 0) : residualPart I J ∣ I :=
  ⟨commonPart I J, (reconstruct I J hI).trans (mul_comm _ _)⟩

theorem residualPart_original_coprime (I J : Ideal O) (hJ : J ≠ 0) :
    IsCoprime (residualPart I J) J := by
  conv_rhs => rw [reconstruct J I hJ]
  exact (commonPart_residualPart_coprime J I).symm.mul_right (residualParts_coprime I J)

theorem commonPart_eq_one_of_empty (I J : Ideal O) (h : commonSupport I J = ∅) :
    commonPart I J = 1 := by simp only [commonPart, h, Finset.prod_empty]

theorem residualPart_eq_of_empty (I J : Ideal O) (hI : I ≠ 0)
    (h : commonSupport I J = ∅) : residualPart I J = I := by
  have he := reconstruct I J hI
  rw [commonPart_eq_one_of_empty I J h, one_mul] at he
  exact he.symm

theorem commonSupport_empty_iff (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    commonSupport I J = ∅ ↔ IsCoprime I J := by
  rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff hI hJ,
    Finset.disjoint_iff_inter_eq_empty]
  rfl

theorem commonPart_one_right (I : Ideal O) : commonPart I 1 = 1 := by
  apply commonPart_eq_one_of_empty
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.inter_empty]

theorem commonPart_one_left (J : Ideal O) : commonPart 1 J = 1 := by
  apply commonPart_eq_one_of_empty
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.empty_inter]

theorem residualPart_one_right (I : Ideal O) (hI : I ≠ 0) : residualPart I 1 = I := by
  apply residualPart_eq_of_empty I 1 hI
  simp only [commonSupport, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.inter_empty]

theorem residualPart_one_left (J : Ideal O) : residualPart 1 J = 1 := by
  simp only [residualPart, primeSupport, normalizedFactors_one, Multiset.toFinset_zero, Finset.empty_sdiff, Finset.prod_empty]

theorem extracted_commonRadical (I J : Ideal O) :
    commonRadical (commonPart I J) (commonPart J I) = commonRadical I J := by
  unfold commonRadical
  rw [commonPart_support, commonPart_support, commonSupport_comm J I, Finset.inter_self]
  rfl

theorem commonRadical_dvd_commonPart (I J : Ideal O) : commonRadical I J ∣ commonPart I J := by
  apply support_product_dvd (commonPart_ne_zero I J)
  rw [commonPart_support]
  exact Finset.Subset.refl _

theorem squarefree_mask_survives (s I J : Ideal O) (hs : Squarefree s)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hsI : s ∣ I) (hsJ : s ∣ J) :
    s ∣ commonRadical I J ∧ s ∣ commonPart I J ∧ s ∣ commonPart J I ∧
      IsCoprime s (residualPart I J) ∧ IsCoprime s (residualPart J I) := by
  have hR := old_mask_dvd_commonRadical s I J hs hI hJ hsI hsJ
  have hC := hR.trans (commonRadical_dvd_commonPart I J)
  have hD : s ∣ commonPart J I := by
    have he : commonRadical I J = commonRadical J I := by
      simp only [commonRadical, Finset.inter_comm]
    exact (he ▸ hR).trans (commonRadical_dvd_commonPart J I)
  exact ⟨hR, hC, hD,
    (commonPart_own_residual_coprime I J).of_isCoprime_of_dvd_left hC,
    (commonPart_own_residual_coprime J I).of_isCoprime_of_dvd_left hD⟩

theorem commonPart_supported (I J : Ideal O) (hI : Supported I) : Supported (commonPart I J) := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_supported I hI _

theorem residualPart_supported (I J : Ideal O) (hI : Supported I) : Supported (residualPart I J) := by
  rw [residualPart_eq_supportResidual]
  exact supportResidual_supported I hI _

theorem primaryGenerator_reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    CompletedGauss.primaryGenerator I =
      CompletedGauss.primaryGenerator (commonPart I J) *
        CompletedGauss.primaryGenerator (residualPart I J) := by
  rw [← CompletedGauss.primaryGenerator_mul, ← reconstruct I J hI]

theorem primary_complete_extraction (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    let C := CompletedGauss.primaryGenerator (commonPart I J)
    let D := CompletedGauss.primaryGenerator (commonPart J I)
    let a := CompletedGauss.primaryGenerator (residualPart I J)
    let b := CompletedGauss.primaryGenerator (residualPart J I)
    CompletedGauss.primaryGenerator I = C * a ∧
    CompletedGauss.primaryGenerator J = D * b ∧
    IsCoprime (C * D) a ∧ IsCoprime (C * D) b ∧ IsCoprime a b := by
  dsimp only
  have hC := commonPart_supported I J hI
  have hD := commonPart_supported J I hJ
  have ha := residualPart_supported I J hI
  have hb := residualPart_supported J I hJ
  have hpC := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ hC)
  have hpD := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ hD)
  have hpa := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ ha)
  have hpb := CompletedGauss.primaryGenerator_spec _
    (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero _ hb)
  refine ⟨primaryGenerator_reconstruct I J hI.1, primaryGenerator_reconstruct J I hJ.1, ?_, ?_, ?_⟩
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpC.1, hpD.1, hpa.1]
    exact commonProduct_leftResidual_coprime I J
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpC.1, hpD.1, hpb.1]
    exact commonProduct_rightResidual_coprime I J
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [hpa.1, hpb.1]
    exact residualParts_coprime I J

theorem common_valuations_pos (I J P : Ideal O) (hP : P ∈ commonSupport I J) :
    0 < valuation I P ∧ 0 < valuation J P := by
  obtain ⟨hI, hJ⟩ := Finset.mem_inter.mp hP
  exact ⟨Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hI),
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hJ)⟩

theorem residualPart_self (I : Ideal O) : residualPart I I = 1 := by
  simp only [residualPart, Finset.sdiff_self, Finset.prod_empty]

theorem commonPart_self (I : Ideal O) (hI : I ≠ 0) : commonPart I I = I := by
  have h := reconstruct I I hI
  rw [residualPart_self, mul_one] at h
  exact h.symm

theorem absNorm_reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm I = Ideal.absNorm (commonPart I J) * Ideal.absNorm (residualPart I J) := by
  have h := congrArg Ideal.absNorm (reconstruct I J hI)
  simpa only [map_mul] using h

theorem absNorm_commonPart_le (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm (commonPart I J) ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm (commonPart_dvd I J hI))

theorem absNorm_residualPart_le (I J : Ideal O) (hI : I ≠ 0) :
    Ideal.absNorm (residualPart I J) ≤ Ideal.absNorm I :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm (residualPart_dvd I J hI))

end SevenEighths.CenteredMomentCompleteCommon

end

end OAI

end Source412

/- Original source: OAI/NumberTheory/DirichletL/Moments/CanonicalFirst.lean; sha256: 33f6d67735150825c63200a09fe785aa1fed8b8601903d4c43ecca6982c909c8 -/
section Source413
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalFirst
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredExceptionalCount
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentFirstReduced CenteredMomentFirstActiveFourier CenteredMomentActive
open CenteredMomentCompleteCommon UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

abbrev CommonIndex (I J : Ideal O) := {P : Ideal O // P∈commonSupport I J}
instance commonIndexMaximal (I J : Ideal O) (P : CommonIndex I J) : P.val.IsMaximal := by
  have hp := prime_of_normalized_factor P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

def leftExponent (I J : Ideal O) (P : CommonIndex I J) := valuation I P.val
def rightExponent (I J : Ideal O) (P : CommonIndex I J) := valuation J P.val

theorem common_good (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ConcretePrimeRowBridge.goodLambda ∉ P.val :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.1

theorem common_odd (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ringChar (O ⧸ P.val)≠2 :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.2

theorem leftExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0<leftExponent I J P :=
  (common_valuations_pos I J P.val P.property).1

theorem rightExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0<rightExponent I J P :=
  (common_valuations_pos I J P.val P.property).2

theorem commonPart_left_product (I J : Ideal O) :
    commonPart I J=∏ P : CommonIndex I J,P.val^leftExponent I J P := by
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation I P)).symm

theorem commonPart_right_product (I J : Ideal O) :
    commonPart J I=∏ P : CommonIndex I J,P.val^rightExponent I J P := by
  unfold commonPart
  rw [commonSupport_comm J I]
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation J P)).symm

abbrev ActiveIndex (I J : Ideal O) :=
  activeSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)
def activePrime (I J : Ideal O) (P : ActiveIndex I J) : Ideal O := P.val.val
instance activePrimeMaximal (I J : Ideal O) (P : ActiveIndex I J) : (activePrime I J P).IsMaximal :=
  commonIndexMaximal I J P.val

def activeConductor (I J : Ideal O) : O := finitePrimeModulus (activePrime I J)
def activeExponent (I J : Ideal O) (P : ActiveIndex I J) :=
  netExponent (leftExponent I J P.val) (rightExponent I J P.val)
theorem activeGood (I J : Ideal O) (hI : Supported I) (P : ActiveIndex I J) :
    ConcretePrimeRowBridge.goodLambda ∉ activePrime I J P := common_good I J hI P.val

theorem activeCoprime (I J : Ideal O) : Pairwise (Function.onFun IsCoprime (activePrime I J)) :=
  activePrimes_pairwise_coprime (fun P : CommonIndex I J => P.val) Subtype.val_injective
    Finset.univ (leftExponent I J) (rightExponent I J)

def activeFunction (I J : Ideal O) (hI : Supported I) : Residue (activeConductor I J) → ℂ :=
  principalSexticRow (activePrime I J) (activeCoprime I J) (activeGood I J hI)
    (activeExponent I J) (activeConductor I J) (span_finitePrimeModulus _)

def residualGenerator (I J : Ideal O) : O := CompletedGauss.primaryGenerator (residualPart I J)

theorem residualGenerator_span (I J : Ideal O) (hI : Supported I) :
    Ideal.span {residualGenerator I J}=residualPart I J :=
  (CompletedGauss.primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (residualPart_supported I J hI))).1

theorem residualGenerator_supported (I J : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {residualGenerator I J}) := by
  rw [residualGenerator_span I J hI]
  exact residualPart_supported I J hI

def residualCharacter (I J : Ideal O) (hI : Supported I) : MulChar (Residue (residualGenerator I J)) ℂ :=
  supportedModulusCharacter _ (residualGenerator_supported I J hI)

@[simp] theorem residualCharacter_mk (I J : Ideal O) (hI : Supported I) (z : O) :
    residualCharacter I J hI (Ideal.Quotient.mk _ z)=idealRowHom z (residualPart I J) := by
  rw [residualCharacter,supportedModulusCharacter_mk,residualGenerator_span I J hI]

theorem original_pair_factor (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (z : O) :
    idealRowHom z I*star (idealRowHom z J)=
      residualCharacter I J hI (Ideal.Quotient.mk _ z)*
        (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ z)*
        (idealRowHom z (∏ P : CommonIndex I J,P.val^leftExponent I J P)*
          star (idealRowHom z (∏ P : CommonIndex I J,P.val^rightExponent I J P))) := by
  let := finite_quotient_span (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
  rw [← MulChar.star_apply',residualCharacter_mk,residualCharacter_mk,
    ← commonPart_left_product,← commonPart_right_product]
  have hi := congrArg (idealRowHom z) (reconstruct I J hI.1)
  have hj := congrArg (idealRowHom z) (reconstruct J I hJ.1)
  simp only [map_mul] at hi hj
  rw [hi,hj,star_mul]
  ring

def reducedFirstSum (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E ∈ (principalSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)).powerset,
    let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
    let k := K/‖eisEmbedding e‖^2
    let a := residualGenerator I J
    let b := residualGenerator J I
    let r := activeConductor I J
    (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
      (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
          paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2))

theorem canonical_pair_reduced_poisson (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,(idealRowHom z I*star (idealRowHom z J))*W (‖eisEmbedding z‖^2/K))=
      reducedFirstSum I J hI hJ W K := by
  simp_rw [original_pair_factor I J hI hJ]
  exact common_residual_reduced_poisson (fun P : CommonIndex I J => P.val) Subtype.val_injective
    (common_good I J hI) (common_odd I J hI) Finset.univ (leftExponent I J) (rightExponent I J)
    (fun P _ => ne_of_gt (leftExponent_pos I J P)) (fun P _ => ne_of_gt (rightExponent_pos I J P))
    (residualGenerator I J) (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ W K hK

theorem activeConductor_span_dvd (I J : Ideal O) :
    Ideal.span {activeConductor I J} ∣ commonPart I J := by
  rw [activeConductor,span_finitePrimeModulus]
  change (∏ P : ActiveIndex I J,P.val.val) ∣ commonPart I J
  rw [Finset.prod_coe_sort]
  refine (Finset.prod_dvd_prod_of_subset _ Finset.univ
    (fun P : CommonIndex I J => P.val) (Finset.subset_univ _)).trans ?_
  rw [commonPart_left_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (leftExponent_pos I J P)

theorem residual_active_coprime (I J : Ideal O) (hI : Supported I) :
    IsCoprime (residualGenerator I J) (activeConductor I J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span I J hI]
  exact (commonPart_own_residual_coprime I J).symm.of_isCoprime_of_dvd_right (activeConductor_span_dvd I J)

theorem opposite_residual_active_coprime (I J : Ideal O) (hJ : Supported J) :
    IsCoprime (residualGenerator J I) (activeConductor I J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span J I hJ]
  exact (commonPart_residualPart_coprime I J).symm.of_isCoprime_of_dvd_right (activeConductor_span_dvd I J)

theorem residual_generators_coprime (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    IsCoprime (residualGenerator I J) (residualGenerator J I) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span I J hI,residualGenerator_span J I hJ]
  exact residualParts_coprime I J

theorem canonical_tripleFourier_norm_le (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (h : O) :
    ‖tripleFourier (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
      (supported_element_ne_zero _ (residualGenerator_supported I J hI))
      (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
      (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h‖ ≤
      ‖eisEmbedding (activeConductor I J)‖*
        ‖residueGauss (residualGenerator I J) (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (residualCharacter I J hI) (Ideal.Quotient.mk _ h)‖*
        ‖residueGauss (residualGenerator J I) (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
          (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ h)‖ := by
  exact tripleFourier_active_norm_le (activePrime I J) (activeCoprime I J) (activeGood I J hI)
    (fun P => common_odd I J hI P.val) (activeExponent I J)
    (netExponent_ne_zero _ _ _) (fun P => netExponent_lt_six _ _)
    (residualGenerator I J) (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    ((residual_generators_coprime I J hI hJ).mul_right (residual_active_coprime I J hI))
    (opposite_residual_active_coprime I J hJ) _ _ h

end SevenEighths.CenteredMomentCanonicalFirst

end

end OAI

end Source413

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstNormalization.lean; sha256: 76210aa2e5f0ec11d2f14ffba7205f5d88b91d386ebc3268c933693ad018c996 -/
section Source414
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstNormalization
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentSupportedCorrelation CenteredMomentFirstReduced CenteredMomentFirstActiveFourier
open CenteredMomentGaussEnergy CenteredMomentPrimitive CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

theorem residueGauss_eq_norm_mul_gaussRow (a : O) (ha : Supported (Ideal.span {a})) (h : O) :
    residueGauss a (supported_element_ne_zero a ha) (supportedModulusCharacter a ha) (Ideal.Quotient.mk _ h)=
      (‖eisEmbedding a‖:ℂ)*gaussRow a ha h := by
  have hn : (‖eisEmbedding a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero a ha)))
  rw [gaussRow,residueGauss_supported_mk,sqrt_absNorm]
  field_simp

theorem normalized_active_coefficient {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
      (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h /
      (‖eisEmbedding (a*(b*r))‖^2:ℝ) =
      (canonicalNormalizedGauss P hcop hg j /
        ((‖eisEmbedding a‖:ℂ)*(‖eisEmbedding b‖:ℂ)*(‖eisEmbedding r‖:ℂ)))*
      (CanonicalRowCompletion.idealRowHom (b*r) (Ideal.span {a})*
        star (CanonicalRowCompletion.idealRowHom (a*r) (Ideal.span {b}))*finiteSexticRow P hg j (a*b))*
      (star (finiteSexticRow P hg j h)*gaussRow a ha h*star (gaussRow b hb (-h))) := by
  dsimp only
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have hna : (‖eisEmbedding a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero a ha)))
  have hnb : (‖eisEmbedding b‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero b hb)))
  have hnr : (‖eisEmbedding (finitePrimeModulus P)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P)))
  rw [tripleFourier_active P hcop hg hchar j hj0 hj6 a b
    (supported_element_ne_zero a ha) (supported_element_ne_zero b hb) har hbr,
    residueGauss_inverse,← map_neg,residueGauss_eq_norm_mul_gaussRow a ha,
    residueGauss_eq_norm_mul_gaussRow b hb,← MulChar.star_apply',
    supportedModulusCharacter_mk,supportedModulusCharacter_mk]
  simp only [canonicalNormalizedGauss,map_mul,norm_mul,star_mul,Complex.star_def,
    Complex.conj_ofReal,Complex.ofReal_pow,Complex.ofReal_mul]
  field_simp

end SevenEighths.CenteredMomentFirstNormalization

end

end OAI

end Source414

/- Original source: OAI/NumberTheory/DirichletL/Moments/ChildAssembly.lean; sha256: 4320a8957d0706d8cc4e92b896f0108269d9975d7975432353aebbe4bfc60d51 -/
section Source415
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildAssembly
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentMobiusRegroup CenteredMomentRowNorm RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def divisorCoefficient {α : Type*} (L : Ideal O) (a : α → O) (c : α → ℂ)
    (χ : RayCharacter) (i : α) : ℂ :=
  if L ∣ Ideal.span {a i} then c i * rayCharacter χ (a i) else 0

theorem rayCharacter_inverse_star (χ : RayCharacter) (a : O) :
    star (rayCharacter (χ⁻¹) a) = rayCharacter χ a := by
  change star ((χ⁻¹) (Ideal.Quotient.mk _ a)) = χ (Ideal.Quotient.mk _ a)
  rw [MulChar.star_apply', inv_inv]

theorem divisor_pair_separation {α β : Type*} (L : Ideal O) (a : α → O) (b : β → O)
    (c : α → ℂ) (d : β → ℂ) (D E h : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (i : α) (j : β) (K : ℂ) :
    (if L ∣ Ideal.span {a i} ∧ L ∣ Ideal.span {b j} then
      completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K else 0) =
      actualCorrelation D E hD hE h *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          pairCoeff (phaseTable D E) χ ξ *
            ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
              star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) * K := by
  by_cases hi : L ∣ Ideal.span {a i}
  · by_cases hj : L ∣ Ideal.span {b j}
    · simp only [hi,hj,and_self,ite_true,divisorCoefficient,star_mul,rayCharacter_inverse_star]
      rw [completeSupportExtension_separated D E h (a i) (b j) hD hE (ha i) (hb j)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    · simp only [hi,hj,and_false,ite_false,divisorCoefficient,ite_true,zero_mul,star_zero,
        mul_zero,Finset.sum_const_zero]
  · simp only [hi,false_and,ite_false,divisorCoefficient,zero_mul,Finset.sum_const_zero,mul_zero]

theorem pair_ray_fubini {α β γ δ : Type*} [Fintype γ] [Fintype δ]
    (S : Finset α) (T : Finset β) (A : γ → δ → ℂ)
    (L : α → γ → ℂ) (R : β → δ → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, ∑ χ : γ, ∑ ξ : δ, A χ ξ * (L i χ * R j ξ) * K i j) =
      ∑ χ : γ, ∑ ξ : δ, A χ ξ * ∑ i ∈ S, ∑ j ∈ T, (L i χ * R j ξ) * K i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := S)]
  simp_rw [Finset.sum_comm (s := S) (t := Finset.univ)]
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem finite_correlation_children {α β : Type*} (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a i - 1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b j - 1)
    (hcopA : ∀ i, IsCoprime (D * E) (a i)) (hcopB : ∀ j, IsCoprime (D * E) (b j))
    (h : O) (c : α → ℂ) (d : β → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) * actualCorrelation D E hD hE h *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
            pairCoeff (phaseTable D E) χ ξ *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
                  star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) * K i j := by
  rw [finite_correlation_mobius S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB h c d K]
  apply Finset.sum_congr rfl
  intro L hL
  simp_rw [divisor_pair_separation L a b c d D E h hD hE ha hb]
  simp_rw [← Finset.mul_sum (s := T), ← Finset.mul_sum (s := S)]
  rw [pair_ray_fubini]
  ring

theorem separated_pair_rowPolynomials {α β : Type*} (S : Finset α) (T : Finset β)
    (L : Ideal O) (a : α → O) (b : β → O) (c : α → ℂ) (d : β → ℂ)
    (χ ξ : RayCharacter) (f : α → ℂ) (g : β → ℂ) (h : O) :
    (∑ i ∈ S, ∑ j ∈ T,
      ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
        star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) *
        (f i * star (g j))) =
      rowPolynomial S a (fun i => divisorCoefficient L a c χ i * f i) h *
        star (rowPolynomial T b (fun j => divisorCoefficient L b d (ξ⁻¹) j * g j) (-h)) := by
  simp only [rowPolynomial, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end SevenEighths.CenteredMomentChildAssembly

end

end OAI

end Source415

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstColumns.lean; sha256: 8e25712197c1f47a50dd27f639795fa0553ff4d263592ebab9c2031d2e9583a6 -/
section Source416
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstColumns
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

def leftCoefficient (e r : O) (ρ : O → ℂ) (a : O) : ℂ :=
  idealRowHom (e*r) (Ideal.span {a})*ρ a

def rightCoefficient (e r : O) (ρ : O → ℂ) (b : O) : ℂ :=
  idealRowHom (e*r) (Ideal.span {b})*star (ρ b)

theorem first_phase_columns (e r a b : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (hpb : ConcretePrimeRowBridge.goodLambda^2∣b-1) (hab : IsCoprime a b) :
    (idealRowHom e (Ideal.span {a})*star (idealRowHom e (Ideal.span {b}))*ρ e)*
      (idealRowHom (b*r) (Ideal.span {a})*star (idealRowHom (a*r) (Ideal.span {b}))*ρ (a*b)) =
      ρ e*sexticReciprocityPhase a b*leftCoefficient e r ρ a*star (rightCoefficient e r ρ b) := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero a ha)
  let : Fintype (CenteredMomentCommonSupport.Residue a) := Fintype.ofFinite _
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero b hb)
  let : Fintype (CenteredMomentCommonSupport.Residue b) := Fintype.ofFinite _
  have hp := supported_opposite_phase b a hb ha hpb hpa hab.symm
  rw [sexticReciprocityPhase_symm b a] at hp
  calc
    _ = ρ e*(idealRowHom b (Ideal.span {a})*star (idealRowHom a (Ideal.span {b})))*
        leftCoefficient e r ρ a*star (rightCoefficient e r ρ b) := by
      simp only [leftCoefficient,rightCoefficient,idealRowHom_argument_mul,hρ,star_mul,star_star]
      ring
    _ = _ := by rw [hp]

def firstPhaseTable (r s : RayRing) : ℂ :=
  (QuadraticAllOddCRT.quadraticRaySign (QuadraticGaussRay.residueQuotientFour r)
    (QuadraticGaussRay.residueQuotientFour s):ℂ)

theorem firstPhaseTable_mk (a b : O) :
    firstPhaseTable (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)=sexticReciprocityPhase a b := by
  simp only [firstPhaseTable,QuadraticGaussRay.residueQuotientFour_mk,sexticReciprocityPhase]

theorem firstPhaseTable_expansion (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    sexticReciprocityPhase a b=∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*rayCharacter χ a*rayCharacter ξ b := by
  have hh := pair_phase_expansion firstPhaseTable a b
  simpa only [supported_rayMask a ha,supported_rayMask b hb,one_mul,firstPhaseTable_mk] using hh

theorem firstPhaseTable_mass :
    (∑ χ : RayCharacter,∑ ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖)≤256 := by
  have hb : ∀ u v : RayRingˣ,‖firstPhaseTable u v‖≤1 := by
    intro u v
    unfold firstPhaseTable QuadraticAllOddCRT.quadraticRaySign
    split_ifs <;> norm_num
  simpa only [mul_one] using pairCoeff_sum_norm_le firstPhaseTable 1 hb

def firstExtension (e r : O) (ρ : O → ℂ) (a b : O) : ℂ :=
  ρ e*sexticReciprocityPhase a b*leftCoefficient e r ρ a*star (rightCoefficient e r ρ b)

theorem firstExtension_separated (e r a b : O) (ρ : O → ℂ)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    firstExtension e r ρ a b=ρ e*∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*(leftCoefficient e r ρ a*rayCharacter χ a)*
        star (rightCoefficient e r ρ b*rayCharacter (ξ⁻¹) b) := by
  unfold firstExtension
  rw [firstPhaseTable_expansion a b ha hb]
  simp only [Finset.mul_sum,Finset.sum_mul,star_mul,CenteredMomentChildAssembly.rayCharacter_inverse_star]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ξ hξ
  ring

end SevenEighths.CenteredMomentFirstColumns

end

end OAI

end Source416

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstFamily.lean; sha256: 33543fe5566733ddeab2be8ac0db95a6b9ff6ec2144a215499b7345d673fbb1b -/
section Source417
namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentPrimaryCharacter CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem exists_supported_row_presentation (η : Character) (m z : O)
    (hm : m≠0) (hz : Supported (Ideal.span {z})) (hmLam : λ₀∣m) (hm2 : (2:O)∣m) :
    ∃ τ : Character,
      τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {z} ∧
      ∀ n : O,elementCoeff τ n=rowTwist (elementHom η) m 1 z n := by
  let r := CompletedGauss.primaryGenerator (Ideal.span {z})
  have hr0 : r≠0 := supported_primaryGenerator_ne_zero _ hz
  have hs := CompletedGauss.primaryGenerator_spec (Ideal.span {z}) hr0
  have hr : Supported (Ideal.span {r}) := hs.1 ▸ hz
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.1
  have hx : (1:O)^4*z=(u:O)*λ₀^0*(2:O)^0*r := by
    simpa only [one_pow,pow_zero,mul_one,mul_comm] using hu.symm
  let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {r}
  have hM : M≠⊥ := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))) (Ideal.span_singleton_eq_bot.not.mpr hr0)
  have hG := rowTwist_periodic η m 1 z hmLam hm2 u 0 0 r hr hs.2 hx
  refine ⟨rowCharacter M hM (rowTwist (elementHom η) m 1 z) hG (rowTwist_unit η m 1 z),?_,?_⟩
  · change M=_
    dsimp only [M]
    rw [hs.1]
  · intro n
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m 1 z n hmLam hm2 u 0 0 r hx h)))

theorem first_period_contains (η : Character) (m e r : O) :
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    M≤Ideal.span {3*r} ∧ M≤Ideal.span {(12:O)} := by
  dsimp only
  constructor
  · calc
      _ ≤ Ideal.span {(72:O)}*Ideal.span {e*r} := by
        rw [mul_assoc]
        exact Ideal.mul_le_right
      _ = Ideal.span {(72:O)*(e*r)} := Ideal.span_singleton_mul_span_singleton _ _
      _ ≤ _ := Ideal.span_singleton_le_span_singleton.mpr ⟨24*e,by ring⟩
  · exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)

theorem exists_first_character (η : Character) (m e r : O)
    (hm : m≠0) (he : Supported (Ideal.span {e})) (hr : Supported (Ideal.span {r}))
    (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (χ : MulChar (Residue r) ℂ) (ξ : RayCharacter) :
    ∃ τ : Character,
      τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r} ∧
      (∀ n : O,elementCoeff τ n=
        rowTwist (elementHom η) m 1 (e*r) n*maskedPrimaryHom r χ n*
          elementCoeff (primaryRayCharacter ξ) n) ∧
      ∀ n : O,Supported (Ideal.span {n}) → λ₀^2∣n-1 →
        elementCoeff τ n=elementCoeff η n*coprimalityMask m n*
          idealRowHom (e*r) (Ideal.span {n})*χ (Ideal.Quotient.mk _ n)*rayCharacter ξ n := by
  obtain ⟨τ₀,hM,hτ⟩ := exists_supported_row_presentation η m (e*r) hm (supported_mul_elements e r he hr) hmLam hm2
  let τ := (τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ)
  have hp := first_period_contains η m e r
  refine ⟨τ,?_,?_,?_⟩
  · change (τ₀.modulus ⊓ (primaryCharacter r (supported_element_ne_zero r hr) χ).modulus) ⊓
      (primaryRayCharacter ξ).modulus=_
    rw [hM,primaryCharacter_modulus,primaryRayCharacter_modulus,inf_eq_left.mpr hp.1,inf_eq_left.mpr hp.2]
  · intro n
    rw [show τ=(τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ) from rfl,
      elementCoeff_product,elementCoeff_product,hτ,primaryCharacter_all]
  · intro n hn hpn
    rw [show τ=(τ₀.product (primaryCharacter r (supported_element_ne_zero r hr) χ)).product (primaryRayCharacter ξ) from rfl,
      elementCoeff_product,elementCoeff_product,hτ,primaryCharacter_primary r _ χ n hpn,
      primaryRayCharacter_primary ξ n hn hpn,rowTwist_extract_sixth_mask _ m 1 (e*r) n hn]
    simp only [one_pow,one_mul]
    rfl

end SevenEighths.CenteredMomentFirstFamily

end

end OAI

end Source417

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstCanonicalFamily.lean; sha256: d0bd45d1726ac00314e26bc88bf5e157ec2a7d312e72429eef9421bf7175155e -/
section Source418
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstCanonicalFamily
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstFamily
open CenteredMomentFirstColumns CenteredMomentPrimitive CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem supported_of_dvd (A B : Ideal O) (hB : Supported B) (hd : A∣B) : Supported A := by
  obtain ⟨Q,hQ⟩ := hd
  rw [hQ] at hB
  exact ((supported_mul_iff A Q).mp hB).1

theorem activeConductor_supported (I J : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {activeConductor I J}) :=
  supported_of_dvd _ _ (commonPart_supported I J hI) (activeConductor_span_dvd I J)

theorem subsetGenerator_span_dvd (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E}∣commonPart I J := by
  rw [primeSubsetGenerator,span_idealGenerator]
  refine (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J => P.val) (Finset.subset_univ _)).trans ?_
  rw [commonPart_left_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (leftExponent_pos I J P)

theorem subsetGenerator_supported (I J : Ideal O) (hI : Supported I)
    (E : Finset (CommonIndex I J)) :
    Supported (Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E}) :=
  supported_of_dvd _ _ (commonPart_supported I J hI) (subsetGenerator_span_dvd I J E)

def canonicalActiveCharacter (I J : Ideal O) (hI : Supported I) :
    MulChar (Residue (activeConductor I J)) ℂ :=
  primitiveCharacter (activePrime I J) (activeCoprime I J) (activeGood I J hI) (activeExponent I J)

@[simp] theorem canonicalActiveCharacter_mk (I J : Ideal O) (hI : Supported I) (n : O) :
    canonicalActiveCharacter I J hI (Ideal.Quotient.mk _ n)=
      finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J) n :=
  primitiveCharacter_mk _ _ _ _ n

theorem exists_canonical_first_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (I J : Ideal O) (hI : Supported I) (E : Finset (CommonIndex I J))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
    let r := activeConductor I J
    let ρ := finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        elementCoeff τ₁ n=elementCoeff η n*coprimalityMask m n*leftCoefficient e r ρ n*rayCharacter ξ₁ n) ∧
      (∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        elementCoeff τ₂ n=elementCoeff η n*coprimalityMask m n*rightCoefficient e r ρ n*rayCharacter ξ₂ n) := by
  dsimp only
  obtain ⟨τ₁,hM₁,_,h₁⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI) ξ₁
  obtain ⟨τ₂,hM₂,_,h₂⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI)⁻¹ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro n hn hp
    rw [h₁ n hn hp,canonicalActiveCharacter_mk,leftCoefficient]
    ring
  · intro n hn hp
    let : Finite (Residue (activeConductor I J)) := finite_quotient_span (finitePrimeModulus_ne_zero (activePrime I J))
    rw [h₂ n hn hp,← MulChar.star_apply',canonicalActiveCharacter_mk,rightCoefficient]
    ring

theorem first_displayed_norm (η : Character) (m : O) (I J : Ideal O)
    (E : Finset (CommonIndex I J)) :
    (η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E*activeConductor I J}).absNorm =
    η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
      ((∏ P∈E,P.val).absNorm*(Ideal.span {activeConductor I J}).absNorm) := by
  rw [← Ideal.span_singleton_mul_span_singleton,primeSubsetGenerator,span_idealGenerator]
  simp only [map_mul]

end SevenEighths.CenteredMomentFirstCanonicalFamily

end

end OAI

end Source418

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceRow.lean; sha256: 5d697f02e352e1ba102adb2400a9eb0d3fd019cf411f5214d7646fbf4b6fcbee -/
section Source419
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentRowNorm HeckeFamily CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_split (η : Character) (m A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m A z t I = rowWeight η m A 1 t I*idealRowHom z I := by
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) =
    ((idealCoeff η I*idealRowHom (m^6*(A*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*idealRowHom z I
  rw [mul_one,← mul_assoc,idealRowHom_argument_mul]
  ring

theorem rowWeight_zero_of_not_supported (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) (I : Ideal O) (hI : ¬Supported I) :
    rowWeight η m A z t I=0 := by
  by_cases h0 : I=0
  · rw [h0,map_zero]
  let n := idealGenerator I
  have hn : n ≠ 0 := idealGenerator_ne_zero I h0
  have hs : Ideal.span {n}=I := span_idealGenerator I
  have hz := rowTwist_zero_of_not_supported (HeckeRowClosure.elementHom η) m 1 (A*z) n
    hmLam hm2 (hs ▸ hI)
  have he : rowTwist (HeckeRowClosure.elementHom η) m 1 (A*z) n =
      idealCoeff η I*idealRowHom (m^6*(A*z)) I := by
    change elementCoeff η n*idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n})=_
    rw [one_pow,mul_one,hs,← idealCoeff_span η hn,hs]
  rw [he] at hz
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=0
  rw [hz,zero_mul]

def supportedColumns (S : Finset (Ideal O)) : Finset (Ideal O) := S.filter Supported

theorem primary_span_supported (I : Ideal O) (hI : Supported I) : Ideal.span {primaryGenerator I}=I := by
  have hn : primaryGenerator I ≠ 0 := by
    have hs : Supported (Ideal.span {idealGenerator I}) := by rw [span_idealGenerator]; exact hI
    have hg := (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff (idealGenerator I)).mpr
      ((supported_span_iff _).mp hs).1
    simpa only [span_idealGenerator] using hg
  exact (primaryGenerator_spec I hn).1

def sourceGenerator (S : Finset (Ideal O)) (I : supportedColumns S) : O := primaryGenerator I

theorem sourceGenerator_supported (S : Finset (Ideal O)) (I : supportedColumns S) :
    Supported (Ideal.span {sourceGenerator S I}) := by
  have hI := (Finset.mem_filter.mp I.property).2
  rw [sourceGenerator,primary_span_supported I hI]
  exact hI

theorem finite_hecke_sum_eq_rowPolynomial (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    (∑ I∈S,c I*rowWeight η m A z t I) =
      rowPolynomial Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) z := by
  have he : (∑ I∈S,c I*rowWeight η m A z t I) =
      ∑ I∈supportedColumns S,c I*rowWeight η m A z t I := by
    symm
    apply Finset.sum_filter_of_ne
    intro I hI hn
    by_contra hs
    exact hn (by rw [rowWeight_zero_of_not_supported η m A z t hmLam hm2 I hs,mul_zero])
  rw [he,← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*rowWeight η m A z t I)]
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,rowWeight_split]
  ring

def finiteHeckeEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O,((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
    W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)

theorem finiteHeckeEnergy_eq (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    finiteHeckeEnergy η m A t S c W K =
      rowEnergy Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) W K := by
  unfold finiteHeckeEnergy rowEnergy
  simp_rw [finite_hecke_sum_eq_rowPolynomial η m A _ t hmLam hm2 S c]

theorem finiteHeckeEnergy_poisson (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          (((K/‖ConcreteTraceCRT.eisEmbedding (sourceGenerator S I*sourceGenerator S J)‖^2:ℝ):ℂ)*
            ∑' h : O,pairFourier (sourceGenerator S I) (sourceGenerator S J)
              (sourceGenerator_supported S I) (sourceGenerator_supported S J) h*
              EisensteinSchwartzPoisson.paperRadialFourier W
                (K*‖ConcreteTraceCRT.eisEmbedding h‖^2/
                  ‖ConcreteTraceCRT.eisEmbedding (sourceGenerator S I*sourceGenerator S J)‖^2)) := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K]
  exact rowEnergy_poisson Finset.univ (sourceGenerator S)
    (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
    (sourceGenerator_supported S) W K hK

end SevenEighths.CenteredMomentSourceRow

end

end OAI

end Source419

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstEnergy.lean; sha256: b1f198845756e185113a9be9a9bd53f2acae0fe64cde707c19fdce9ae1f31bc5 -/
section Source420
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstEnergy
open CenteredMomentCanonicalFirst CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentHeckeExpansion HeckeFamily ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem finiteHeckeEnergy_reduced_poisson (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          reducedFirstSum I J (Finset.mem_filter.mp I.property).2
            (Finset.mem_filter.mp J.property).2 W K := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K,
    rowEnergy_expand Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
      (sourceGenerator_supported S) W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sourceGenerator,sourceGenerator,
    primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2,
    canonical_pair_reduced_poisson]
  exact hK

end SevenEighths.CenteredMomentFirstEnergy

end

end OAI

end Source420

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonSectors.lean; sha256: 8342a1e3c554fd784fa55516b70c3c71bdc2b6de681616f6271f764b4ddb13fc -/
section Source421
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonSectors
open CenteredMomentCompleteCommon CenteredMomentSupport IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem primeSupport_mul (I J : Ideal O) (hI : I≠0) (hJ : J≠0) :
    primeSupport (I*J)=primeSupport I∪primeSupport J := by
  simp only [primeSupport,normalizedFactors_mul hI hJ,Multiset.toFinset_add]

theorem supportExtract_of_subset (I : Ideal O) (hI : I≠0) (S : Finset (Ideal O))
    (hS : primeSupport I⊆S) : supportExtract I S=I := by
  unfold supportExtract
  rw [Multiset.filter_eq_self.mpr (fun P hP => hS (Multiset.mem_toFinset.mpr hP))]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_of_disjoint (I : Ideal O) (S : Finset (Ideal O))
    (hS : Disjoint (primeSupport I) S) : supportExtract I S=1 := by
  unfold supportExtract
  rw [Multiset.filter_eq_nil.mpr (fun P hP => Finset.disjoint_left.mp hS (Multiset.mem_toFinset.mpr hP))]
  rfl

theorem reconstructed_commonSupport (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    commonSupport (C*a) (D*b)=primeSupport C := by
  unfold commonSupport
  rw [primeSupport_mul C a hC ha,primeSupport_mul D b hD hb,← hCD]
  have h₁ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa
  have h₂ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hb).mpr hCb
  have h₃ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff ha hb).mpr hab
  ext P
  simp only [Finset.mem_inter,Finset.mem_union]
  constructor
  · rintro ⟨hc|ha',hd|hb'⟩
    · exact hc
    · exact hc
    · exact hd
    · exact False.elim (Finset.disjoint_left.mp h₃ ha' hb')
  · exact fun hp => ⟨Or.inl hp,Or.inl hp⟩

theorem reconstructed_commonParts (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    commonPart (C*a) (D*b)=C ∧ commonPart (D*b) (C*a)=D := by
  have hs := reconstructed_commonSupport C D a b hC hD ha hb hCD hCa hCb hab
  have h₁ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa
  have h₂ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hb).mpr hCb
  constructor
  · rw [commonPart_eq_supportExtract,hs,supportExtract_mul C a hC ha,
      supportExtract_of_subset C hC _ (Finset.Subset.refl _),supportExtract_of_disjoint a _ h₁.symm,mul_one]
  · rw [commonPart_eq_supportExtract,commonSupport_comm (D*b) (C*a),hs,
      supportExtract_mul D b hD hb,
      supportExtract_of_subset D hD _ (by rw [hCD]),supportExtract_of_disjoint b _ h₂.symm,mul_one]

theorem reconstructed_residualParts (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    residualPart (C*a) (D*b)=a ∧ residualPart (D*b) (C*a)=b := by
  obtain ⟨h₁,h₂⟩ := reconstructed_commonParts C D a b hC hD ha hb hCD hCa hCb hab
  constructor
  · apply mul_left_cancel₀ hC
    have he := reconstruct (C*a) (D*b) (mul_ne_zero hC ha)
    rw [h₁] at he
    exact he.symm
  · apply mul_left_cancel₀ hD
    have he := reconstruct (D*b) (C*a) (mul_ne_zero hD hb)
    rw [h₂] at he
    exact he.symm

end SevenEighths.CenteredMomentCommonSectors

end

end OAI

end Source421

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSectors.lean; sha256: a981e8a977db16c32fee8d270536ff8bab7862166a9263913852925f21ac0141 -/
section Source422
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstSectors
open CenteredMomentCompleteCommon CenteredMomentCommonSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def residualPool (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O)) : Finset (Ideal O) :=
  S.preimage (fun a => C*a) (by intro a ha b hb he;exact mul_left_cancel₀ hC he)

@[simp] theorem mem_residualPool (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O)) (a : Ideal O) :
    a∈residualPool C hC S ↔ C*a∈S := Finset.mem_preimage

def pairSector (C D : Ideal O) (S T : Finset (Ideal O)) : Finset (Ideal O × Ideal O) :=
  (S.product T).filter (fun p => commonPart p.1 p.2=C ∧ commonPart p.2 p.1=D)

def residualPairDomain (C D : Ideal O) (hC : C≠0) (hD : D≠0) (S T : Finset (Ideal O)) :
    Finset (Ideal O × Ideal O) :=
  ((residualPool C hC S).product (residualPool D hD T)).filter
    (fun p => IsCoprime C p.1 ∧ IsCoprime C p.2 ∧ IsCoprime p.1 p.2)

theorem residualPair_image (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (S T : Finset (Ideal O))
    (hS : ∀ I∈S,I≠0) (hT : ∀ J∈T,J≠0) :
    (residualPairDomain C D hC hD S T).image (fun p => (C*p.1,D*p.2))=pairSector C D S T := by
  ext p
  rcases p with ⟨I,J⟩
  constructor
  · intro hp
    obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp hp
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    obtain ⟨hpools,hCa,hCb,hab⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hpools
    have has : C*a∈S := (mem_residualPool C hC S a).mp ha
    have hbs : D*b∈T := (mem_residualPool D hD T b).mp hb
    have ha0 : a≠0 := right_ne_zero_of_mul (hS _ has)
    have hb0 : b≠0 := right_ne_zero_of_mul (hT _ hbs)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨has,hbs⟩,
      reconstructed_commonParts C D a b hC hD ha0 hb0 hCD hCa hCb hab⟩
  · intro hp
    obtain ⟨hpools,hCI,hDJ⟩ := Finset.mem_filter.mp hp
    obtain ⟨hIS,hJT⟩ := Finset.mem_product.mp hpools
    have hi : C*residualPart I J=I := by rw [← hCI];exact (reconstruct I J (hS I hIS)).symm
    have hj : D*residualPart J I=J := by rw [← hDJ];exact (reconstruct J I (hT J hJT)).symm
    refine Finset.mem_image.mpr ⟨(residualPart I J,residualPart J I),?_,Prod.ext hi hj⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_,?_,residualParts_coprime I J⟩
    · exact (mem_residualPool C hC S _).mpr (by dsimp only;rw [hi];exact hIS)
    · exact (mem_residualPool D hD T _).mpr (by dsimp only;rw [hj];exact hJT)
    · rw [← hCI]
      exact commonPart_own_residual_coprime I J
    · rw [← hCI]
      exact commonPart_residualPart_coprime I J

theorem pairSector_sum (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (S T : Finset (Ideal O))
    (hS : ∀ I∈S,I≠0) (hT : ∀ J∈T,J≠0) (F : Ideal O → Ideal O → ℂ) :
    (∑ p∈pairSector C D S T,F p.1 p.2)=
      ∑ p∈residualPairDomain C D hC hD S T,F (C*p.1) (D*p.2) := by
  rw [← residualPair_image C D hC hD hCD S T hS hT,Finset.sum_image]
  intro p hp q hq he
  exact Prod.ext (mul_left_cancel₀ hC (congrArg Prod.fst he))
    (mul_left_cancel₀ hD (congrArg Prod.snd he))

theorem pairSector_double_sum (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (S T : Finset (Ideal O))
    (hS : ∀ I∈S,I≠0) (hT : ∀ J∈T,J≠0) (F : Ideal O → Ideal O → ℂ) :
    (∑ p∈pairSector C D S T,F p.1 p.2)=
      ∑ a∈residualPool C hC S,∑ b∈residualPool D hD T,
        if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then F (C*a) (D*b) else 0 := by
  rw [pairSector_sum C D hC hD hCD S T hS hT,residualPairDomain,Finset.sum_filter]
  exact Finset.sum_product _ _ _

def commonLabels (S T : Finset (Ideal O)) : Finset (Ideal O × Ideal O) :=
  (S.product T).image (fun p => (commonPart p.1 p.2,commonPart p.2 p.1))

theorem commonLabels_data (S T : Finset (Ideal O)) (C D : Ideal O)
    (h : (C,D)∈commonLabels S T) :
    C≠0 ∧ D≠0 ∧ primeSupport C=primeSupport D := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  rcases Prod.mk.inj he with ⟨rfl,rfl⟩
  exact ⟨commonPart_ne_zero _ _,commonPart_ne_zero _ _,commonParts_equal_support _ _⟩

theorem sum_common_sectors (S T : Finset (Ideal O)) (F : Ideal O → Ideal O → ℂ) :
    (∑ I∈S,∑ J∈T,F I J)=
      ∑ p∈commonLabels S T,∑ q∈pairSector p.1 p.2 S T,F q.1 q.2 := by
  have hh := Finset.sum_fiberwise_of_maps_to
    (s:=S.product T) (t:=commonLabels S T)
    (g:=fun p : Ideal O × Ideal O => (commonPart p.1 p.2,commonPart p.2 p.1))
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    (fun p : Ideal O × Ideal O => F p.1 p.2)
  symm
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro p hp
    rcases p with ⟨C,D⟩
    congr 1
    ext q
    simp only [pairSector,Finset.mem_filter,Prod.mk.injEq]
  · exact (Finset.sum_product S T (fun p : Ideal O × Ideal O => F p.1 p.2)).symm

end SevenEighths.CenteredMomentFirstSectors

end

end OAI

end Source422

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSectorEnergy.lean; sha256: bf3c46c3195ad19f8130dc8ad8efed67347c5310a7690d5a940515ecdb13ba26 -/
section Source423
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorEnergy
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentCommonSectors CenteredMomentCompleteCommon
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentActive CenteredMomentFourier IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def originalKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O,(idealRowHom z I*star (idealRowHom z J))*W (‖eisEmbedding z‖^2/K)

theorem energy_common_sectors (η : Character) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
            originalKernel q.1 q.2 W K := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K,
    rowEnergy_expand Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
      (sourceGenerator_supported S) W K hK]
  have hspan (I : supportedColumns S) : Ideal.span {sourceGenerator S I} = I :=
    primary_span_supported I (Finset.mem_filter.mp I.property).2
  simp_rw [hspan]
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K)=_
  let F := fun I J : Ideal O =>
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K
  have he (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort (supportedColumns S) (F I)
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,F I J)=_
  simp_rw [he]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ _

theorem sector_independent_columns (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) (hCD : primeSupport C=primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*originalKernel q.1 q.2 W K) =
      rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
        ∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
          if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then
            ((c (C*a)*rowWeight η m A 1 t a)*star (c (D*b)*rowWeight η m A 1 t b))*
              originalKernel (C*a) (D*b) W K else 0 := by
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I J => ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [map_mul,star_mul,mul_zero]
  ring

theorem fixed_common_parts (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) : commonPart C D=C ∧ commonPart D C=D := by
  simpa only [mul_one] using reconstructed_commonParts C D 1 1 hC hD one_ne_zero one_ne_zero
    hCD (isCoprime_one_right) (isCoprime_one_right) (isCoprime_one_left)

def fixedFirstSum (C D : Ideal O) (hC : Supported C) (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E ∈ (principalSupport (Finset.univ : Finset (CommonIndex C D)) (leftExponent C D) (rightExponent C D)).powerset,
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let k := K/‖eisEmbedding e‖^2
    let r := activeConductor C D
    (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC) e*
      (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter a ha)
          (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC) h*
          paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2))

theorem originalKernel_fixed_first (C D : Ideal O) (hC : Supported C) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    originalKernel (C*Ideal.span {a}) (D*Ideal.span {b}) W K=fixedFirstSum C D hC a b ha hb W K := by
  let := finite_quotient_span (supported_element_ne_zero b hb)
  obtain ⟨h₁,h₂⟩ := fixed_common_parts C D hC.1 hD hCD
  have he := common_residual_reduced_poisson (fun P : CommonIndex C D => P.val) Subtype.val_injective
    (common_good C D hC) (common_odd C D hC) Finset.univ (leftExponent C D) (rightExponent C D)
    (fun P _ => ne_of_gt (leftExponent_pos C D P)) (fun P _ => ne_of_gt (rightExponent_pos C D P))
    a b (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ W K hK
  change _=fixedFirstSum C D hC a b ha hb W K at he
  rw [← he]
  unfold originalKernel
  apply tsum_congr
  intro z
  rw [← MulChar.star_apply',supportedModulusCharacter_mk,supportedModulusCharacter_mk,
    ← commonPart_left_product,← commonPart_right_product,h₁,h₂]
  simp only [map_mul,star_mul]
  ring

end SevenEighths.CenteredMomentFirstSectorEnergy

end

end OAI

end Source423

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSectorTransform.lean; sha256: c0db0a3c60605dd37439fcea2075bc01feffcdb3f17e54c1f32714a14147852a -/
section Source424
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorTransform
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve HeckeFamily CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentSupportedCorrelation IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem residualPool_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : Supported (a:Ideal O) := by
  have ha := (Finset.mem_filter.mp ((mem_residualPool C hC (supportedColumns S) a).mp a.property)).2
  exact ((supported_mul_iff C a).mp ha).2

def residualElement (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : O := CompletedGauss.primaryGenerator a

theorem residualElement_span (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : Ideal.span {residualElement C hC S a}=a :=
  primary_span_supported a (residualPool_supported C hC S a)

theorem residualElement_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : Supported (Ideal.span {residualElement C hC S a}) := by
  rw [residualElement_span]
  exact residualPool_supported C hC S a

def sectorFixedTransform (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ a : residualPool C hC.1 (supportedColumns S),
    ∑ b : residualPool D hD.1 (supportedColumns S),
      if IsCoprime C (a:Ideal O) ∧ IsCoprime C (b:Ideal O) ∧ IsCoprime (a:Ideal O) (b:Ideal O) then
        ((c (C*a)*rowWeight η m A 1 t a)*star (c (D*b)*rowWeight η m A 1 t b))*
          fixedFirstSum C D hC (residualElement C hC.1 S a) (residualElement D hD.1 S b)
            (residualElement_supported C hC.1 S a) (residualElement_supported D hD.1 S b) W K
      else 0

theorem sector_fixed_transform (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*originalKernel q.1 q.2 W K) =
      rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
        sectorFixedTransform η m A t S c C D hC hD W K := by
  rw [sector_independent_columns η m A t S c C D hC.1 hD.1 hCD W K]
  congr 1
  unfold sectorFixedTransform
  let F := fun a b : Ideal O =>
    if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then
      ((c (C*a)*rowWeight η m A 1 t a)*star (c (D*b)*rowWeight η m A 1 t b))*originalKernel (C*a) (D*b) W K else 0
  change (∑ a∈residualPool C hC.1 (supportedColumns S),∑ b∈residualPool D hD.1 (supportedColumns S),F a b)=_
  rw [← Finset.sum_coe_sort _ (fun a => ∑ b∈residualPool D hD.1 (supportedColumns S),F a b)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_coe_sort _ (F a)]
  apply Finset.sum_congr rfl
  intro b hb
  dsimp only [F]
  split_ifs
  · have hh := originalKernel_fixed_first C D hC hD.1 hCD
      (residualElement C hC.1 S a) (residualElement D hD.1 S b)
      (residualElement_supported C hC.1 S a) (residualElement_supported D hD.1 S b) W K hK
    rw [residualElement_span,residualElement_span] at hh
    rw [hh]
  · rfl

theorem commonLabels_supported (S : Finset (Ideal O))
    (p : commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported p.val.1 ∧ Supported p.val.2 := by
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp p.property
  have hq₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
  have hq₂ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).2
  rw [← he]
  exact ⟨commonPart_supported _ _ hq₁,commonPart_supported _ _ hq₂⟩

theorem energy_fixed_transforms (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight η m A 1 t p.val.1*star (rowWeight η m A 1 t p.val.2)*
          sectorFixedTransform η m A t S c p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K := by
  rw [energy_common_sectors η m A t hmLam hm2 S c W K hK]
  rw [← Finset.sum_coe_sort _ (fun p : Ideal O × Ideal O => ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
    ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*originalKernel q.1 q.2 W K)]
  apply Finset.sum_congr rfl
  intro p hp
  exact sector_fixed_transform η m A t S c p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2
    (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2 W K hK

end SevenEighths.CenteredMomentFirstSectorTransform

end

end OAI

end Source424

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonAllocation.lean; sha256: 83a63da7d06b94c5b30a21fe471daa80d8bf49217152b657221940da2ba3051f -/
section Source425
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocation
open CenteredMomentSupport CenteredMomentCommonSectors CenteredMomentExtraction
open CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem extract_coprime_product (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportExtract (C*a) (primeSupport C)=C := by
  rw [supportExtract_mul C a hC ha,
    supportExtract_of_subset C hC _ (Finset.Subset.refl _),
    supportExtract_of_disjoint a _ ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa).symm,
    mul_one]

theorem residual_coprime_product (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportResidual (C*a) (primeSupport C)=a := by
  apply mul_left_cancel₀ hC
  have he := support_reconstruct (C*a) (mul_ne_zero hC ha) (primeSupport C)
  rwa [extract_coprime_product C a hC ha hCa] at he

theorem tuple_products {ι : Type*} [Fintype ι] (v : ι → Ideal O) (C a : Ideal O)
    (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hv : ∏ i,v i=C*a) :
    (∏ i,supportExtract (v i) (primeSupport C))=C ∧
      (∏ i,supportResidual (v i) (primeSupport C))=a := by
  have hv0 : ∏ i,v i≠0 := hv.symm ▸ mul_ne_zero hC ha
  have hi (i : ι) : v i≠0 := Finset.prod_ne_zero_iff.mp hv0 i (Finset.mem_univ _)
  constructor
  · rw [← supportExtract_prod Finset.univ v (fun i _ => hi i),hv]
    exact extract_coprime_product C a hC ha hCa
  · rw [← supportResidual_prod Finset.univ v (fun i _ => hi i),hv]
    exact residual_coprime_product C a hC ha hCa

theorem residual_factor_coprime (C I : Ideal O) (hC : C≠0) :
    IsCoprime C (supportResidual I (primeSupport C)) := by
  have hh := extracted_residual_coprime C I (primeSupport C)
  rwa [supportExtract_of_subset C hC _ (Finset.Subset.refl _)] at hh

theorem slot_plain_products {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i∈T,Prime (p i)) (I J C a : Ideal O) (hI : I≠0) (hJ : J≠0)
    (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a)
    (hprod : (∏ i∈T,p i)*I*J=C*a) :
    (∏ i∈T.filter (fun i => p i∈primeSupport C),p i)*
        supportExtract I (primeSupport C)*supportExtract J (primeSupport C)=C ∧
      (∏ i∈T.filter (fun i => p i∉primeSupport C),p i)*
        supportResidual I (primeSupport C)*supportResidual J (primeSupport C)=a := by
  have hp0 : (∏ i∈T,p i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i hi => (hp i hi).ne_zero)
  have hf := (prime_slot_allocation T p hp (primeSupport C)).1
  have hl := (prime_slot_allocation T p hp (primeSupport C)).2
  constructor
  · have he := extract_coprime_product C a hC ha hCa
    rw [← hprod,supportExtract_mul _ J (mul_ne_zero hp0 hI) hJ,
      supportExtract_mul _ I hp0 hI,hf] at he
    exact he
  · have he := residual_coprime_product C a hC ha hCa
    rw [← hprod,supportResidual_mul _ J (mul_ne_zero hp0 hI) hJ,
      supportResidual_mul _ I hp0 hI,hl] at he
    exact he

theorem centered_source_allocation {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (ν : ι → ℂ) (η : Character) (m A z : O) (t : ℝ)
    (I J C a : Ideal O) (hI : I≠0) (hJ : J≠0)
    (hprod : (∏ i∈T,p i)*I*J=C*a)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∏ i∈T,ν i)*rowWeight η m A z t ((∏ i∈T,p i)*I*J)*
      idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
      ((∏ i∈T.filter (fun i => p i∈primeSupport C),ν i)*rowWeight η m A z t C)*
        ((∏ i∈T.filter (fun i => p i∉primeSupport C),ν i)*rowWeight η m A z t a*
          idealRectangle W₁ W₂
            (X₁/Ideal.absNorm (supportExtract I (primeSupport C)))
            (X₂/Ideal.absNorm (supportExtract J (primeSupport C)))
            (Y₁/Ideal.absNorm (supportExtract I (primeSupport C)))
            (Y₂/Ideal.absNorm (supportExtract J (primeSupport C)))
            (supportResidual I (primeSupport C)) (supportResidual J (primeSupport C))) := by
  have hrect := idealRectangle_extract W₁ W₂ X₁ X₂ Y₁ Y₂
    (supportExtract I (primeSupport C)) (supportExtract J (primeSupport C))
    (supportResidual I (primeSupport C)) (supportResidual J (primeSupport C))
  rw [support_reconstruct I hI,support_reconstruct J hJ] at hrect
  rw [hprod,map_mul,hrect,← Finset.prod_filter_mul_prod_filter_not T (fun i => p i∈primeSupport C) ν]
  ring

end SevenEighths.CenteredMomentCommonAllocation

end

end OAI

end Source425

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonAllocationBox.lean; sha256: ac3cad6b0398b8cb1856ed218f76e8dbe0623d2bddc1752fb633917e6279ab2d -/
section Source426
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocationBox
open CenteredMomentCommonAllocation CenteredMomentSupport CenteredMomentCommonSectors
open CenteredMomentFirstSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def sourceFiber (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) :
    Finset (ι → Ideal O) :=
  (Fintype.piFinset S).filter (fun v => ∀ i,supportExtract (v i) (primeSupport C)=B i)

def residualBoxes (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O)
    (hB : ∀ i,B i≠0) : Finset (ι → Ideal O) :=
  Fintype.piFinset (fun i => (residualPool (B i) (hB i) (S i)).filter (IsCoprime C))

theorem residualBoxes_image (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) :
    (residualBoxes S C B hB).image (fun v i => B i*v i)=sourceFiber S C B := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    have hui := Fintype.mem_piFinset.mp hu
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact (mem_residualPool (B i) (hB i) (S i) _).mp (Finset.mem_filter.mp (hui i)).1
    · intro i
      have hp := Finset.mem_filter.mp (hui i)
      have hsrc := (mem_residualPool (B i) (hB i) (S i) _).mp hp.1
      have hu0 : u i≠0 := right_ne_zero_of_mul (hS i _ hsrc)
      rw [supportExtract_mul _ _ (hB i) hu0,supportExtract_of_subset _ (hB i) _ (hBs i),
        supportExtract_of_disjoint _ _ ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hu0).mpr hp.2).symm,mul_one]
  · intro hv
    obtain ⟨hv,hvB⟩ := Finset.mem_filter.mp hv
    have hvi := Fintype.mem_piFinset.mp hv
    let u := fun i => supportResidual (v i) (primeSupport C)
    have hi (i : ι) : B i*u i=v i := by
      rw [← hvB i]
      exact support_reconstruct _ (hS i _ (hvi i)) _
    refine Finset.mem_image.mpr ⟨u,?_,funext hi⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_residualPool (B i) (hB i) (S i) _).mpr
      rw [hi]
      exact hvi i
    · exact residual_factor_coprime C (v i) hC

theorem sourceFiber_sum (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈sourceFiber S C B,F v)=
      ∑ u∈residualBoxes S C B hB,F (fun i => B i*u i) := by
  rw [← residualBoxes_image S hS C hC B hB hBs,Finset.sum_image]
  intro u hu v hv he
  funext i
  exact mul_left_cancel₀ (hB i) (congrFun he i)

theorem sourceFiber_product_sum (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) (hprod : ∏ i,B i=C)
    (a : Ideal O) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0)=
      ∑ u∈residualBoxes S C B hB,if (∏ i,u i)=a then F (fun i => B i*u i) else 0 := by
  rw [sourceFiber_sum S hS C hC B hB hBs]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Finset.prod_mul_distrib,hprod,mul_right_inj' hC]

end SevenEighths.CenteredMomentCommonAllocationBox

end

end OAI

end Source426

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonAllocationSum.lean; sha256: 3715eafaf13bc6503c36c3624de106647a520ddc6681af4e9e776611fbab62fc -/
section Source427
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocation CenteredMomentCommonAllocationBox CenteredMomentSupport
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def allocationLabels (S : ι → Finset (Ideal O)) (C : Ideal O) : Finset (ι → Ideal O) :=
  (Fintype.piFinset S).image (fun v i => supportExtract (v i) (primeSupport C))

def actualAllocations (S : ι → Finset (Ideal O)) (C : Ideal O) : Finset (ι → Ideal O) :=
  (allocationLabels S C).filter (fun B => ∏ i,B i=C)

theorem allocation_data (S : ι → Finset (Ideal O)) (C : Ideal O)
    (B : ι → Ideal O) (hB : B∈allocationLabels S C) :
    (∀ i,B i≠0) ∧ (∀ i,primeSupport (B i)⊆primeSupport C) := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hB
  refine ⟨fun i => supportExtract_ne_zero _ _,?_⟩
  intro i
  rw [supportExtract_support]
  exact Finset.inter_subset_right

 theorem sum_source_fibers (S : ι → Finset (Ideal O)) (C : Ideal O)
    (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,F v)=∑ B∈allocationLabels S C,∑ v∈sourceFiber S C B,F v := by
  have hh := Finset.sum_fiberwise_of_maps_to (s:=Fintype.piFinset S) (t:=allocationLabels S C)
    (g:=fun v i => supportExtract (v i) (primeSupport C))
    (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) F
  symm
  convert hh using 1
  apply Finset.sum_congr rfl
  intro B hB
  congr 1
  ext v
  simp only [sourceFiber,Finset.mem_filter,funext_iff]

theorem sum_actual_allocations (S : ι → Finset (Ideal O))
    (C a : Ideal O) (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a)
    (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,if (∏ i,v i)=C*a then F v else 0)=
      ∑ B∈actualAllocations S C,
        ∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0 := by
  rw [sum_source_fibers S C]
  symm
  apply Finset.sum_filter_of_ne
  intro B hB hn
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hp : (∏ i,v i)=C*a := by
    by_contra hh
    exact hne (ite_eq_right hh)
  have he := (tuple_products v C a hC ha hCa hp).1
  have hb := (Finset.mem_filter.mp hv).2
  simpa only [hb] using he

theorem original_coefficient_allocated (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,if (∏ i,v i)=C*a then F v else 0)=
      ∑ B : actualAllocations S C,
        ∑ u∈residualBoxes S C B
          (allocation_data S C B (Finset.mem_filter.mp B.property).1).1,
          if (∏ i,u i)=a then F (fun i => B.val i*u i) else 0 := by
  rw [sum_actual_allocations S C a hC ha hCa F]
  rw [← Finset.sum_coe_sort (actualAllocations S C)
    (fun B => ∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0)]
  apply Finset.sum_congr rfl
  intro B hB
  exact sourceFiber_product_sum S hS C hC B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).2
    (Finset.mem_filter.mp B.property).2 a F

theorem actualAllocations_card (S : ι → Finset (Ideal O)) (C : Ideal O) (hC : C≠0) :
    (actualAllocations S C).card≤(idealDivisors C).card^(Fintype.card ι) := by
  let f (B : actualAllocations S C) : ι → idealDivisors C := fun i => ⟨B.val i,by
    apply (mem_idealDivisors hC).mpr
    have hh := Finset.dvd_prod_of_mem B.val (Finset.mem_univ i)
    rw [(Finset.mem_filter.mp B.property).2] at hh
    exact hh⟩
  have hf : Function.Injective f := by
    intro B D he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun] using Fintype.card_le_of_injective f hf

theorem actualAllocations_small_power [Nonempty ι] (ε : ℝ) (hε : 0<ε) :
    ∃ D : ℝ,0<D ∧ ∀ (S : ι → Finset (Ideal O)) (C : Ideal O),C≠0 →
      ((actualAllocations S C).card:ℝ)≤D*(Ideal.absNorm C:ℝ)^ε := by
  have hr : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos
  let δ := ε/(Fintype.card ι:ℝ)
  have hδ : 0<δ := div_pos hε hr
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨D^(Fintype.card ι),pow_pos hD _,?_⟩
  intro S C hC
  have hd : δ*(Fintype.card ι:ℝ)=ε := by dsimp only [δ];field_simp
  calc
    _ ≤ ((idealDivisors C).card:ℝ)^(Fintype.card ι) := by exact_mod_cast actualAllocations_card S C hC
    _ ≤ (D*(Ideal.absNorm C:ℝ)^δ)^(Fintype.card ι) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv C hC) _
    _ = _ := by rw [mul_pow,← Real.rpow_mul_natCast (Nat.cast_nonneg _),hd]

end SevenEighths.CenteredMomentCommonAllocationSum

end

end OAI

end Source427

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonPrimeSlots.lean; sha256: 5e4be055c4fe5ae02b5830194641fc8ebccae9856888e4c8de825022e20a521a -/
section Source428
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonPrimeSlots
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSupport IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem residual_original_mem (S : ι → Finset (Ideal O)) (C : Ideal O)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0) (u : ι → Ideal O)
    (hu : u∈residualBoxes S C B hB) (i : ι) : B i*u i∈S i :=
  (CenteredMomentFirstSectors.mem_residualPool _ _ _ _).mp
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu i)).1

theorem prime_coordinate_cases (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C)
    (u : ι → Ideal O) (hu : u∈residualBoxes S C B hB)
    (i : ι) (hp : ∀ I∈S i,Prime I) :
    (B i=1 ∧ Prime (u i)) ∨ (u i=1 ∧ Prime (B i)) := by
  have hsrc := residual_original_mem S C B hB u hu i
  have hprime := hp _ hsrc
  by_cases hBi : B i=1
  · exact Or.inl ⟨hBi,by simpa only [hBi,one_mul] using hprime⟩
  · have hv : (fun j => B j*u j)∈sourceFiber S C B := by
      rw [← residualBoxes_image S hS C hC B hB hBs]
      exact Finset.mem_image.mpr ⟨u,hu,rfl⟩
    have he := (Finset.mem_filter.mp hv).2 i
    rw [supportExtract_prime _ hprime] at he
    have hmem : B i*u i∈primeSupport C := by
      by_contra hn
      rw [ite_eq_right hn] at he
      exact hBi he.symm
    rw [ite_eq_left hmem] at he
    have hu1 : u i=1 := mul_left_cancel₀ (hB i) (he.trans (mul_one (B i)).symm)
    exact Or.inr ⟨hu1,by simpa only [hu1,mul_one] using hprime⟩

def liveSlots (T : Finset ι) (B : ι → Ideal O) : Finset ι := T.filter (fun i => B i=1)
def frozenSlots (T : Finset ι) (B : ι → Ideal O) : Finset ι := T.filter (fun i => B i≠1)

theorem slot_coefficient_product (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C)
    (u : ι → Ideal O) (hu : u∈residualBoxes S C B hB)
    (T : Finset ι) (hp : ∀ i∈T,∀ I∈S i,Prime I) (β : ι → Ideal O → ℂ) :
    (∏ i∈T,β i (B i*u i))=
      (∏ i∈frozenSlots T B,β i (B i))*(∏ i∈liveSlots T B,β i (u i)) := by
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => B i=1) (fun i => β i (B i*u i)),mul_comm]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro i hi
    have hTi := (Finset.mem_filter.mp hi).1
    have hBi := (Finset.mem_filter.mp hi).2
    have hu1 : u i=1 := by
      rcases prime_coordinate_cases S hS C hC B hB hBs u hu i (hp i hTi) with h|h
      · exact False.elim (hBi h.1)
      · exact h.1
    rw [hu1,mul_one]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2,one_mul]

theorem slot_residual_product (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C)
    (u : ι → Ideal O) (hu : u∈residualBoxes S C B hB)
    (T : Finset ι) (hp : ∀ i∈T,∀ I∈S i,Prime I) :
    (∏ i∈T,u i)=∏ i∈liveSlots T B,u i := by
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hBi : B i≠1 := by
    intro he
    exact hnot (Finset.mem_filter.mpr ⟨hi,he⟩)
  rcases prime_coordinate_cases S hS C hC B hB hBs u hu i (hp i hi) with h|h
  · exact False.elim (hBi h.1)
  · exact h.1

end SevenEighths.CenteredMomentCommonPrimeSlots

end

end OAI

end Source428

/- Original source: OAI/NumberTheory/DirichletL/Moments/ZeroMode.lean; sha256: 707cff1bebaaee8bbe026a054e2bfc02eaa7972d55a6fe0dea5474b1c4f12d80 -/
section Source429
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentZeroMode
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcreteTraceCRT CubicEisenstein
open CenteredMomentRowNorm CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentFourier
open UniqueFactorizationMonoid CenteredExceptionalCount CenteredExceptionalProfile
local notation "O" => ActualEisensteinCubic.O

@[simp] theorem pairResidue_mul (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x y : Residue (a * b)) :
    pairResidue a b ha hb (x * y) =
      pairResidue a b ha hb x * pairResidue a b ha hb y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, pairResidue_mk, pairResidue_mk, pairResidue_mk,
    idealRowHom_argument_mul, idealRowHom_argument_mul, star_mul]
  ring

@[simp] theorem pairFourier_zero (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    pairFourier a b ha hb 0 = ∑' x : Residue (a * b), pairResidue a b ha hb x := by
  simp [pairFourier, quotientTrace]

theorem pairResidue_unit_eq_one_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (u : (Residue (a * b))ˣ) :
    pairResidue a b ha hb u = 1 := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype] at hm
  have he : pairResidue a b ha hb u * (∑ x : Residue (a * b), pairResidue a b ha hb x) =
      ∑ x : Residue (a * b), pairResidue a b ha hb x := by
    simpa only [Finset.mul_sum, pairResidue_mul] using
      u.mulLeft_bijective.sum_comp (pairResidue a b ha hb)
  exact (mul_right_cancel₀ hm (he.trans (one_mul _).symm))

theorem rows_agree_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (n : O)
    (hn : IsCoprime (Ideal.span {n}) (Ideal.span {a} * Ideal.span {b})) :
    idealRowHom n (Ideal.span {a}) = idealRowHom n (Ideal.span {b}) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {a * b}) n) := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr
    simpa only [Ideal.span_singleton_mul_span_singleton] using hn
  have he := pairResidue_unit_eq_one_of_mean_ne_zero a b ha hb hm hunit.unit
  rw [hunit.unit_spec, pairResidue_mk] at he
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {b}) n) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hn.of_mul_right_right
  have hj : idealRowHom n (Ideal.span {b}) * star (idealRowHom n (Ideal.span {b})) = 1 := by
    change supportedModulusCharacter b hb (Ideal.Quotient.mk _ n) *
      star (supportedModulusCharacter b hb (Ideal.Quotient.mk _ n)) = 1
    rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
    exact MulChar.one_apply hu
  exact mul_right_cancel₀ (by intro hz; simp [hz] at hj) (he.trans hj.symm)

theorem valuation_profile_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (P : Ideal O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    valuation (Ideal.span {a}) P % 6 = valuation (Ideal.span {b}) P % 6 := by
  apply valuation_mod_six_of_unit_agreement 1
    (Ideal.span {a} * Ideal.span {b}) _ _ P (mul_ne_zero ha.1 hb.1) ha hb
    hg hodd isCoprime_one_left
  intro n _ hn
  exact rows_agree_of_mean_ne_zero a b ha hb hm n hn

theorem powerful_product_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) :
    CompletedGauss.PowerfulIdeal (Ideal.span {a} * Ideal.span {b}) := by
  have hs := (supported_mul_iff _ _).mpr ⟨ha, hb⟩
  refine ⟨hs.1, ?_⟩
  intro P hP
  obtain ⟨hmax, hg, hodd⟩ := supported_factors_good _ hs P hP
  let := hmax
  have he := valuation_profile_of_mean_ne_zero a b ha hb hm P hg hodd
  have hp := Multiset.count_pos.mpr hP
  rw [normalizedFactors_mul ha.1 hb.1, Multiset.count_add] at hp ⊢
  unfold valuation at he
  omega

theorem powerful_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O × Ideal O)) (Y : ℝ), 1 ≤ Y →
      (∀ p ∈ S, CompletedGauss.PowerfulIdeal (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ Y) →
      (S.card : ℝ) ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hp⟩ := CompletedGauss.powerful_ideal_count (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro S Y hY hS
  let T := S.image (fun p : Ideal O × Ideal O => p.1 * p.2)
  have hT (I : Ideal O) (hI : I ∈ T) :
      CompletedGauss.PowerfulIdeal I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    exact hS p hp
  have hcard : (S.card : ℝ) = ∑ I ∈ T,
      ((S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I)).card : ℝ) := by
    calc
      _ = ∑ _p ∈ S, (1 : ℝ) := by simp
      _ = ∑ I ∈ T, ∑ _p ∈ S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), (1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun p hp =>
          Finset.mem_image_of_mem (fun p : Ideal O × Ideal O => p.1 * p.2) hp) _).symm
      _ = _ := by simp
  rw [hcard]
  calc
    _ ≤ ∑ I ∈ T, D * Y ^ (ε / 2) := by
      apply Finset.sum_le_sum
      intro I hI
      calc
        _ ≤ ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ) := by
          exact_mod_cast product_fiber_card S I (hT I hI).1.1
        _ ≤ D * (Ideal.absNorm I : ℝ) ^ (ε / 2) := hd I (hT I hI).1.1
        _ ≤ D * Y ^ (ε / 2) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hT I hI).2 (by positivity)) hD.le
    _ = (T.card : ℝ) * (D * Y ^ (ε / 2)) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε / 2)) * (D * Y ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right (hp T Y hY hT) (by positivity)
    _ = (C * D) * (Y ^ (1 / 2 + ε / 2) * Y ^ (ε / 2)) := by ring
    _ = (C * D) * Y ^ (1 / 2 + ε) := by
      rw [← Real.rpow_add (by linarith : 0 < Y)]
      congr 2
      ring

theorem pairFourier_zero_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    ‖pairFourier a b ha hb 0‖ ≤ (Ideal.absNorm (Ideal.span {a * b}) : ℝ) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype]
  calc
    _ ≤ ∑ x : Residue (a * b), ‖pairResidue a b ha hb x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue (a * b), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [pairResidue_mk, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans
        (idealRowHom_norm _ _)
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem scaled_zero_mean_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (K : ℝ) (hK : 0 ≤ K) :
    ‖((K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) : ℂ) * pairFourier a b ha hb 0‖ ≤ K := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {a * b}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero
        (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    eisEmbedding_norm_sq_eq_absNorm_span, abs_of_nonneg (div_nonneg hK hn.le)]
  calc
    _ ≤ (K / (Ideal.absNorm (Ideal.span {a * b}) : ℝ)) *
        (Ideal.absNorm (Ideal.span {a * b}) : ℝ) :=
      mul_le_mul_of_nonneg_left (pairFourier_zero_norm_le a b ha hb) (div_nonneg hK hn.le)
    _ = K := div_mul_cancel₀ _ hn.ne'

theorem nonzero_mean_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (Y : ℝ), 1 ≤ Y →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      ((S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)).card : ℝ)
        ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := powerful_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb Y hY hinj hN
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  let f := fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})
  have hf : Set.InjOn f (T : Set (α × β)) := by
    intro p hp q hq he
    exact hinj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he
  have ht : (T.image f).card = T.card := Finset.card_image_of_injOn hf
  have hbound := hc (T.image f) Y hY (by
    intro I hI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    have hp' := Finset.mem_filter.mp hp
    exact ⟨powerful_product_of_mean_ne_zero (a p.1) (b p.2) (ha p.1) (hb p.2) hp'.2,
      hN p hp'.1⟩)
  simpa only [ht] using hbound

theorem first_zero_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (d : α × β → ℂ)
      (Y K B : ℝ), 1 ≤ Y → 0 ≤ K → 0 ≤ B →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      (∀ p ∈ S, ‖d p‖ ≤ B) →
      ‖∑ p ∈ S, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ ≤
        C * K * B * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := nonzero_mean_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb d Y K B hY hK hB hinj hN hd
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  have hsum : (∑ p ∈ S, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)) =
      ∑ p ∈ T, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hpt
    have hz : pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 = 0 := by
      simpa only [T, Finset.mem_filter, hp, true_and, not_not] using hpt
    rw [hz, mul_zero, mul_zero]
  rw [hsum]
  calc
    _ ≤ ∑ p ∈ T, ‖d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, B * K := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_mul (hd p (Finset.mem_filter.mp hp).1)
        (scaled_zero_mean_norm_le _ _ _ _ K hK) (norm_nonneg _) hB
    _ = (T.card : ℝ) * (B * K) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε)) * (B * K) :=
      mul_le_mul_of_nonneg_right (hc S a b ha hb Y hY hinj hN) (mul_nonneg hB hK)
    _ = C * K * B * Y ^ (1 / 2 + ε) := by ring

theorem productColumnCoefficient_sextic_row_sum (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (z : O) :
    (∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J)) =
      ∑ K ∈ (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2),
        productColumnCoefficient S T β K * idealRowHom z K := by
  rw [← Finset.sum_product (f := fun p : Ideal O × Ideal O =>
    β p.1 p.2 * idealRowHom z (p.1 * p.2))]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun p (hp : p ∈ S ×ˢ T) => Finset.mem_image_of_mem (fun p : Ideal O × Ideal O => p.1 * p.2) hp)]
  apply Finset.sum_congr rfl
  intro K hK
  rw [productColumnCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem productColumnCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ),
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ 1) →
      ∀ (I : Ideal O) (X : ℝ), I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ X →
        ‖productColumnCoefficient S T β I‖ ≤ D * X ^ ε := by
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨D, hD, ?_⟩
  intro S T β hβ I X hI hX
  exact (productColumnCoefficient_norm S T β hβ I hI).trans
    ((hd I hI).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hX hε.le) hD.le))

def idealColumn (S : Finset (Ideal O)) (I : S) : O :=
  ConcretePrimeRowBridge.idealGenerator I.val

@[simp] theorem idealColumn_span (S : Finset (Ideal O)) (I : S) :
    Ideal.span {idealColumn S I} = I.val :=
  ConcretePrimeRowBridge.span_idealGenerator _

theorem idealColumn_supported (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (I : S) :
    Supported (Ideal.span {idealColumn S I}) := by
  rw [idealColumn_span]
  exact hS I.val I.property

def idealZeroEnergy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (K : ℝ) : ℂ :=
  ∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
    (((K / ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (idealColumn S I) (idealColumn S J)
        (idealColumn_supported S hS I) (idealColumn_supported S hS J) 0)

theorem ideal_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
      (c : Ideal O → ℂ) (X K B : ℝ), 1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) →
      (∀ I ∈ S, ‖c I‖ ≤ B) →
      ‖idealZeroEnergy S hS c K‖ ≤ C * K * B ^ 2 * X ^ (1 + ε) := by
  obtain ⟨C, hC, hc⟩ := first_zero_sum_bound (ε / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro S hS c X K B hX hK hB hN hd
  have hinj : Set.InjOn (fun p : S × S =>
      (Ideal.span {idealColumn S p.1}, Ideal.span {idealColumn S p.2}))
        (↑(Finset.univ : Finset (S × S)) : Set (S × S)) := by
    intro p _ q _ he
    apply Prod.ext
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.fst he)
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.snd he)
  have hNpair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      (Ideal.absNorm (Ideal.span {idealColumn S p.1} * Ideal.span {idealColumn S p.2}) : ℝ) ≤ X ^ 2 := by
    rw [idealColumn_span, idealColumn_span, map_mul, Nat.cast_mul, pow_two]
    exact mul_le_mul (hN _ p.1.property) (hN _ p.2.property) (Nat.cast_nonneg _) (by linarith)
  have hdPair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      ‖c p.1.val * star (c p.2.val)‖ ≤ B ^ 2 := by
    rw [norm_mul, norm_star, pow_two]
    exact mul_le_mul (hd _ p.1.property) (hd _ p.2.property) (norm_nonneg _) hB
  have hh := hc Finset.univ (idealColumn S) (idealColumn S)
    (idealColumn_supported S hS) (idealColumn_supported S hS)
    (fun p : S × S => c p.1.val * star (c p.2.val)) (X ^ 2) K (B ^ 2)
    (by nlinarith) hK (sq_nonneg _) hinj hNpair hdPair
  have hp : (X ^ 2) ^ (1 / 2 + ε / 2 : ℝ) = X ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ X)]
    congr 1
    ring
  simpa only [idealZeroEnergy, Fintype.sum_prod_type, hp] using hh

theorem productColumnCoefficient_norm_le (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) (I : Ideal O) (hI : I ≠ 0) :
    ‖productColumnCoefficient S T β I‖ ≤ B * (IdealMobiusDivisorSum.idealDivisors I).card := by
  unfold productColumnCoefficient
  calc
    _ ≤ ∑ p ∈ (S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), ‖β p.1 p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ (S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), B := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact hβ p.1 hh.1 p.2 hh.2
    _ = B * ((S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I)).card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast product_fiber_card (S ×ˢ T) I hI) hB

theorem productColumns_supported (S T : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J) :
    ∀ I ∈ (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2), Supported I := by
  intro I hI
  obtain ⟨⟨J, K⟩, hp, rfl⟩ := Finset.mem_image.mp hI
  have hh := Finset.mem_product.mp hp
  exact (supported_mul_iff J K).mpr ⟨hS J hh.1, hT K hh.2⟩

def productZeroEnergy (S T : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
    (β : Ideal O → Ideal O → ℂ) (K : ℝ) : ℂ :=
  idealZeroEnergy ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2))
    (productColumns_supported S T hS hT) (productColumnCoefficient S T β) K

theorem product_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖productZeroEnergy S T hS hT β K‖ ≤ C * K * B ^ 2 * X ^ (1 + ε) := by
  obtain ⟨C, hC, hc⟩ := ideal_zero_energy_bound (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 4) (by positivity)
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro S T hS hT β X K B hX hK hB hN hβ
  let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
  have hs := productColumns_supported S T hS hT
  have hn (I : Ideal O) (hI : I ∈ P) : (Ideal.absNorm I : ℝ) ≤ X := by
    obtain ⟨⟨J, L⟩, hp, rfl⟩ := Finset.mem_image.mp hI
    have hh := Finset.mem_product.mp hp
    exact hN J hh.1 L hh.2
  have hb (I : Ideal O) (hI : I ∈ P) :
      ‖productColumnCoefficient S T β I‖ ≤ B * (D * X ^ (ε / 4)) := by
    apply (productColumnCoefficient_norm_le S T β B hB hβ I (hs I hI).1).trans
    apply mul_le_mul_of_nonneg_left _ hB
    exact (hd I (hs I hI).1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hn I hI) (by positivity)) hD.le)
  have hh := hc P hs (productColumnCoefficient S T β) X K (B * (D * X ^ (ε / 4)))
    hX hK (by positivity) hn hb
  change ‖productZeroEnergy S T hS hT β K‖ ≤ _ at hh
  apply hh.trans_eq
  have hx0 : 0 < X := by linarith
  have hp : (X ^ (ε / 4)) ^ 2 * X ^ (1 + ε / 2) = X ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    ring
  calc
    C * K * (B * (D * X ^ (ε / 4))) ^ 2 * X ^ (1 + ε / 2) =
        (C * D ^ 2) * K * B ^ 2 * ((X ^ (ε / 4)) ^ 2 * X ^ (1 + ε / 2)) := by ring
    _ = _ := by rw [hp]

theorem normalized_product_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) * productZeroEnergy S T hS hT β K‖ ≤
        C * K * B ^ 2 * X ^ ε := by
  obtain ⟨C, hC, hc⟩ := product_zero_energy_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro S T hS hT β X K B hX hK hB hN hβ
  have hx0 : 0 < X := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
  calc
    _ ≤ X⁻¹ * (C * K * B ^ 2 * X ^ (1 + ε)) :=
      mul_le_mul_of_nonneg_left (hc S T hS hT β X K B hX hK hB hN hβ) (by positivity)
    _ = C * K * B ^ 2 * X ^ ε := by
      rw [Real.rpow_add hx0, Real.rpow_one]
      field_simp

theorem aggregated_rowPolynomial (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (z : O) :
    let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
    rowPolynomial Finset.univ (idealColumn P)
      (fun I : P => productColumnCoefficient S T β I.val) z =
      ∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J) := by
  dsimp only
  rw [rowPolynomial]
  simp only [idealColumn_span]
  rw [Finset.sum_coe_sort ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2))
    (fun I : Ideal O => productColumnCoefficient S T β I * idealRowHom z I)]
  exact (productColumnCoefficient_sextic_row_sum S T β z).symm

theorem aggregated_rowEnergy (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (W : SchwartzMap ℝ ℂ) (K : ℝ) :
    let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
    rowEnergy Finset.univ (idealColumn P)
      (fun I : P => productColumnCoefficient S T β I.val) W K =
      ∑' z : O, ((‖∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J)‖ ^ 2 : ℝ) : ℂ) *
        W (‖eisEmbedding z‖ ^ 2 / K) := by
  simp only [CenteredMomentRowNorm.rowEnergy, aggregated_rowPolynomial]

theorem idealZeroEnergy_first_frequency (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ)
    (W : SchwartzMap ℝ ℂ) (K : ℝ) :
    (∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
      (((K / ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2 : ℝ) : ℂ) *
        (pairFourier (idealColumn S I) (idealColumn S J)
          (idealColumn_supported S hS I) (idealColumn_supported S hS J) 0 *
          EisensteinSchwartzPoisson.paperRadialFourier W
            (K * ‖eisEmbedding (0 : O)‖ ^ 2 /
              ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2)))) =
      idealZeroEnergy S hS c K * EisensteinSchwartzPoisson.paperRadialFourier W 0 := by
  simp [idealZeroEnergy, Finset.sum_mul, mul_assoc]

theorem normalized_product_zero_mode_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (W : SchwartzMap ℝ ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) *
        (productZeroEnergy S T hS hT β K * EisensteinSchwartzPoisson.paperRadialFourier W 0)‖ ≤
        C * K * B ^ 2 * ‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖ * X ^ ε := by
  obtain ⟨C, hC, hc⟩ := normalized_product_zero_energy_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro S T hS hT β W X K B hX hK hB hN hβ
  rw [← mul_assoc, norm_mul]
  calc
    _ ≤ (C * K * B ^ 2 * X ^ ε) * ‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖ :=
      mul_le_mul_of_nonneg_right (hc S T hS hT β X K B hX hK hB hN hβ) (norm_nonneg _)
    _ = _ := by ring

end SevenEighths.CenteredMomentZeroMode

end

end OAI

end Source429

/- Original source: OAI/NumberTheory/DirichletL/Moments/Tail.lean; sha256: 6f2f1e08b58832d1dcd29b811cba68e20a9c2c439fa407f95b6e62daf1761976 -/
section Source430
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTail
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
open CenteredMomentSupportedCorrelation

theorem residueGauss_norm_le (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    ‖residueGauss d hd χ h‖ ≤ (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  let := finite_quotient_span hd
  let : Fintype (Residue d) := Fintype.ofFinite _
  rw [residueGauss, tsum_fintype]
  calc
    _ ≤ ∑ x : Residue d, ‖χ x * quotientTrace d hd (h * x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue d, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
      rw [norm_mul, (quotientTrace d hd).norm_apply, mul_one]
      exact QuadraticInitialBound.norm_finite_character_le_one χ x
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem normalizedResidueGauss_norm_le (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    ‖normalizedResidueGauss d hd χ h‖ ≤ Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {d}) := by
    exact_mod_cast (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hd)))
  rw [normalizedResidueGauss, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hn)).mpr
  rw [Real.mul_self_sqrt hn.le]
  exact residueGauss_norm_le d hd χ h

theorem normalizedResidueGauss_div_root_norm_le_one (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    ‖normalizedResidueGauss d hd χ h /
      (Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) : ℂ)‖ ≤ 1 := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {d}) := by
    exact_mod_cast (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hd)))
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_one (Real.sqrt_pos.mpr hn)).mpr (normalizedResidueGauss_norm_le d hd χ h)

theorem fullModulusCorrelation_norm_le (u v : O) (_hu : u ≠ 0) (_hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : O) :
    ‖fullModulusCorrelation u v χu χv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  unfold fullModulusCorrelation fullCorrelation
  calc
    _ ≤ ∑ x : Residue u, ‖∑ y : Residue v,
      if scaledResidue u v (u * v) rfl x - scaledResidue v u (u * v) (mul_comm u v) y =
        Ideal.Quotient.mk _ j then χu x * star (χv y) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, ∑ _y : Residue v, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro y hy
      split_ifs
      · rw [norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (QuadraticInitialBound.norm_finite_character_le_one χu x)).trans
          (QuadraticInitialBound.norm_finite_character_le_one χv y)
      · simp
    _ = _ := by
      simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem actualCorrelation_norm_le (u v : O)
    (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
    (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})) (j : O) :
    ‖actualCorrelation u v hu hv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  let := finite_quotient_span (supported_element_ne_zero u hu)
  let := finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  unfold actualCorrelation
  exact fullModulusCorrelation_norm_le u v (supported_element_ne_zero u hu)
    (supported_element_ne_zero v hv) _ _ j

theorem weighted_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T B : ℝ), 0 < K → 0 ≤ T → 0 ≤ B →
      ∀ c : O → ℂ, (∀ h, ‖c h‖ ≤ B) →
      ‖∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
        c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K T B hK hT hB c hc
  let S := {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2}
  have hs : Summable (fun h : S => ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    (paperRadialFourier_lattice_summable_norm W K hK).subtype _
  have hpoint (h : S) : ‖c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
      B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc _) (norm_nonneg _)
  have hsum : Summable (fun h : S =>
      ‖c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint (hs.mul_left B)
  calc
    _ ≤ ∑' h : S, ‖c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' h : S, B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      hsum.tsum_le_tsum hpoint (hs.mul_left B)
    _ = B * ∑' h : S, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := tsum_mul_left
    _ ≤ _ := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (ht W K T hK hT) hB

theorem weighted_set_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (D : Set O) (K T B : ℝ), 0 < K → 0 ≤ T → 0 ≤ B →
      (∀ h ∈ D, T ≤ K * ‖eisEmbedding h‖ ^ 2) →
      ∀ c δ : O → ℂ, (∀ h ∈ D, ‖c h‖ ≤ B) → (∀ h ∈ D, ‖δ h‖ ≤ 1) →
      ‖∑' h : D, δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W D K T B hK hT hB hD c δ hc hδ
  let L := {h : O | T ≤ K * ‖eisEmbedding h‖ ^ 2}
  let f : D → L := fun h => ⟨h.val, hD h.val h.property⟩
  have hfi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : L => z.val) h)
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  have hp (h : D) : ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
      B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_left (norm_nonneg _) (hδ h.val h.property)).trans (hc h.val h.property))
      (norm_nonneg _)
  have hsum : Summable (fun h : D =>
      ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp ((hs.subtype D).mul_left B)
  calc
    _ ≤ ∑' h : D, ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' h : D, B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      hsum.tsum_le_tsum hp ((hs.subtype D).mul_left B)
    _ = B * ∑' h : D, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := tsum_mul_left
    _ ≤ B * ∑' h : L, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      mul_le_mul_of_nonneg_left ((hs.subtype D).tsum_le_tsum_of_inj f hfi
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype L)) hB
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left (ht W K T hK hT) hB using 1
      · rfl
      · ring

theorem uniform_sector_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (D : Set O) (K₀ T B : ℝ), 0 < K₀ → 0 ≤ T → 0 ≤ B →
      (∀ h ∈ D, T ≤ K₀ * ‖eisEmbedding h‖ ^ 2) →
      ∀ K : ℝ, K₀ ≤ K →
      ∀ c δ : O → ℂ, (∀ h ∈ D, ‖c h‖ ≤ B) → (∀ h ∈ D, ‖δ h‖ ≤ 1) →
      ‖∑' h : D, δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K₀) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := weighted_set_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W D K₀ T B hK₀ hT hB hD K hK c δ hc hδ
  have hD' (h : O) (hh : h ∈ D) : T ≤ K * ‖eisEmbedding h‖ ^ 2 :=
    (hD h hh).trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _))
  apply (ht W D K T B (hK₀.trans_le hK) hT hB hD' c δ hc hδ).trans
  apply div_le_div_of_nonneg_left (by positivity)
    (by have : 0 < min 1 K₀ := lt_min zero_lt_one hK₀; positivity)
  gcongr

theorem actual_correlation_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
      ∀ (u v : O) (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
        (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})),
      ‖∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
        actualCorrelation u v hu hv (-h.val) *
          paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        ((Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ)) *
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := weighted_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K T hK hT u v hu hv
  exact ht W K T _ hK hT (by positivity) _
    (fun h => actualCorrelation_norm_le u v hu hv (-h))

theorem actual_first_gauss_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
      ∀ {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (hinj : Function.Injective P) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
        (_hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
        (B : Finset ι) (c d : ι → ℕ)
        (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ),
      let r := CenteredMomentInitial.activeModulus P B c d
      let ξ := CenteredMomentInitial.commonCharacter P hinj hg B c d
      ‖∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
        (normalizedResidueGauss r (CenteredMomentInitial.activeModulus_ne_zero P B c d) ξ
            (Ideal.Quotient.mk _ h.val) *
          (normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ h.val) /
            (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)) *
          star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-h.val)) /
            (Real.sqrt (Ideal.absNorm (Ideal.span {b}) : ℝ) : ℂ))) *
          paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := weighted_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K T hK hT ι P _ hinj hg hchar B c d a b ha hb χa χb
  dsimp only
  simpa only [one_mul] using ht W K T 1 hK hT zero_le_one
    (fun h => normalizedResidueGauss _ (CenteredMomentInitial.activeModulus_ne_zero P B c d)
      (CenteredMomentInitial.commonCharacter P hinj hg B c d) (Ideal.Quotient.mk _ h) *
      (normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ h) /
        (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)) *
      star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-h)) /
        (Real.sqrt (Ideal.absNorm (Ideal.span {b}) : ℝ) : ℂ))) (by
      intro h
      rw [norm_mul, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        ((mul_le_of_le_one_left (norm_nonneg _)
          (CenteredMomentInitial.common_gauss_norm_le_one P hinj hg hchar B c d h)).trans
          (normalizedResidueGauss_div_root_norm_le_one a ha χa _))).trans
        (normalizedResidueGauss_div_root_norm_le_one b hb χb _))

end SevenEighths.CenteredMomentTail
end

end OAI

end Source430

/- Original source: OAI/NumberTheory/DirichletL/Moments/AddedZero.lean; sha256: cc30397fa25cffed29ea7d089d7bbfc16a58b925fd45a9f93d3fed9d780f2145 -/
section Source431
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAddedZero
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentRowNorm CenteredMomentFourier CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentGaussEnergy CenteredMomentZeroMode
open CenteredExceptionalCount CenteredMomentRectangle CenteredMomentExtraction
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

lemma supported_one_ideal : Supported (1 : Ideal O) := by
  refine ⟨one_ne_zero, ?_⟩
  intro P hP
  simp only [normalizedFactors_one, Multiset.notMem_zero] at hP

lemma supported_one_element : Supported (Ideal.span {(1 : O)}) := by
  simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using supported_one_ideal

theorem pairFourier_one (u : O) (hu : Supported (Ideal.span {u})) (h : O) :
    pairFourier u 1 hu supported_one_element h =
      ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) h := by
  have hone (x : Residue (1 : O)) : supportedModulusCharacter 1 supported_one_element x = 1 := by
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [supportedModulusCharacter_mk]
    simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using (idealRowHom n).map_one
  have aux (v : O) (hd : u ∣ v) (hv : v ≠ 0) (he : v = u) :
      (∑' x : Residue v, supportedModulusCharacter u hu (frequencyReduction u v hd x) *
        CubicEisenstein.quotientTrace v hv (Ideal.Quotient.mk _ h * x)) =
      residueGauss u (supported_element_ne_zero u hu) (supportedModulusCharacter u hu)
        (Ideal.Quotient.mk _ h) := by
    subst v
    apply tsum_congr
    intro x
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [frequencyReduction_mk]
  rw [← residueGauss_supported_mk u hu h]
  simpa only [pairFourier, pairResidue, hone, star_one, mul_one] using
    aux (u * 1) (dvd_mul_right u 1)
      (mul_ne_zero (supported_element_ne_zero u hu) (supported_element_ne_zero 1 supported_one_element))
      (mul_one u)

theorem gaussRow_zero_sixthRemainder (u : O) (hu : Supported (Ideal.span {u}))
    (hzero : gaussRow u hu 0 ≠ 0) : sixthRemainder (Ideal.span {u}) = 1 := by
  have hg : ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) 0 ≠ 0 := by
    intro hz
    apply hzero
    simp only [gaussRow, hz, zero_div]
  have hm : pairFourier u 1 hu supported_one_element 0 ≠ 0 := by
    rwa [pairFourier_one]
  apply sixthRemainder_eq_of_prime_profile one_ne_zero
  intro P hP
  by_cases hmem : P ∈ normalizedFactors (Ideal.span {u})
  · obtain ⟨hmax, hlam, hodd⟩ := supported_factors_good _ hu P hmem
    let := hmax
    have hv := valuation_profile_of_mean_ne_zero u 1 hu supported_one_element hm P hlam hodd
    simpa only [Ideal.span_singleton_one, ← Ideal.one_eq_top, valuation,
      normalizedFactors_one, Multiset.count_zero, Nat.zero_mod] using hv
  · simp only [valuation, Multiset.count_eq_zero.mpr hmem, normalizedFactors_one,
      Multiset.count_zero, Nat.zero_mod]

theorem gaussRow_zero_ideal_sixth_power (u : O) (hu : Supported (Ideal.span {u}))
    (hzero : gaussRow u hu 0 ≠ 0) :
    sixthQuotient (Ideal.span {u}) ^ 6 = Ideal.span {u} := by
  simpa only [gaussRow_zero_sixthRemainder u hu hzero, one_mul] using
    sixth_normal_form (Ideal.span {u}) hu.1

theorem gaussRow_norm_le (u : O) (hu : Supported (Ideal.span {u})) (h : O) :
    ‖gaussRow u hu h‖ ≤ Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) := by
  have hb := CenteredMomentTail.normalizedResidueGauss_norm_le u
    (supported_element_ne_zero u hu) (supportedModulusCharacter u hu) (Ideal.Quotient.mk _ h)
  simpa only [normalizedResidueGauss, residueGauss_supported_mk,
    gaussRow] using hb

theorem squarefree_divisor_sixth_of_gauss_zero (u : O)
    (hu : Supported (Ideal.span {u})) (hzero : gaussRow u hu 0 ≠ 0)
    (s : Ideal O) (hs : Squarefree s) (hd : s ∣ Ideal.span {u}) :
    s ^ 6 ∣ Ideal.span {u} := by
  have he := gaussRow_zero_ideal_sixth_power u hu hzero
  rw [← he] at hd ⊢
  exact pow_dvd_pow_of_dvd ((hs.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp hd) 6

def idealGaussRow (I : Ideal O) (hI : Supported I) (h : O) : ℂ :=
  gaussRow (primaryGenerator I) ((supported_span_primaryGenerator_iff I).mpr hI) h

lemma idealGaussRow_norm_le (I : Ideal O) (hI : Supported I) (h : O) :
    ‖idealGaussRow I hI h‖ ≤ Real.sqrt (Ideal.absNorm I : ℝ) := by
  have hb := gaussRow_norm_le (primaryGenerator I) ((supported_span_primaryGenerator_iff I).mpr hI) h
  simpa only [idealGaussRow, (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1] using hb

lemma idealGaussRow_zero_sixthRemainder (I : Ideal O) (hI : Supported I)
    (hz : idealGaussRow I hI 0 ≠ 0) : sixthRemainder I = 1 := by
  have hb := gaussRow_zero_sixthRemainder (primaryGenerator I)
    ((supported_span_primaryGenerator_iff I).mpr hI) hz
  simpa only [idealGaussRow, (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1] using hb

def tupleProduct {r : ℕ} (v : Fin r → Ideal O) : Ideal O := ∏ i, v i

lemma tupleEntry_dvd {r : ℕ} (v : Fin r → Ideal O) (i : Fin r) : v i ∣ tupleProduct v :=
  Finset.dvd_prod_of_mem v (Finset.mem_univ i)

theorem tuple_product_fiber_card {r : ℕ} (S : Finset (Fin r → Ideal O))
    (I : Ideal O) (hI : I ≠ 0) :
    (S.filter (fun v => tupleProduct v = I)).card ≤ (idealDivisors I).card ^ r := by
  let T := S.filter (fun v => tupleProduct v = I)
  let f (v : T) : Fin r → idealDivisors I := fun i => ⟨v.val i, by
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp v.property).2]
    exact tupleEntry_dvd v.val i⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, T] using
    Fintype.card_le_of_injective f hf

def idealAddedZero (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) : ℂ :=
  ∑ I : S, c I.val * idealGaussRow I.val (hS I.val I.property) 0

theorem idealAddedZero_norm_le (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (B Y : ℝ) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    ‖idealAddedZero S hS c‖ ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y) := by
  let F := S.filter (fun I => sixthRemainder I = 1)
  have hcount : (F.card : ℝ) ≤ 128 * Y ^ (1 / 6 : ℝ) := by
    simpa only [map_one, Nat.cast_one, div_one] using
      ideal_count_fixed_remainder F 1 one_ne_zero Y hY
        (fun I hI => (hS I (Finset.mem_filter.mp hI).1).1)
        (fun I hI => (Finset.mem_filter.mp hI).2)
        (fun I hI => hN I (Finset.mem_filter.mp hI).1)
  have hb (I : S) : ‖c I.val * idealGaussRow I.val (hS I.val I.property) 0‖ ≤
      if sixthRemainder I.val = 1 then B * Real.sqrt Y else 0 := by
    by_cases hr : sixthRemainder I.val = 1
    · simp only [hr, ite_true, norm_mul]
      exact mul_le_mul (hc I.val I.property)
        ((idealGaussRow_norm_le _ _ _).trans (Real.sqrt_le_sqrt (hN I.val I.property)))
        (norm_nonneg _) hB
    · have hz : idealGaussRow I.val (hS I.val I.property) 0 = 0 := by
        by_contra hn
        exact hr (idealGaussRow_zero_sixthRemainder _ _ hn)
      simp only [hr, ite_false, hz, mul_zero, norm_zero, le_refl]
  calc
    ‖idealAddedZero S hS c‖ ≤ ∑ I : S,
        ‖c I.val * idealGaussRow I.val (hS I.val I.property) 0‖ := norm_sum_le _ _
    _ ≤ ∑ I : S, if sixthRemainder I.val = 1 then B * Real.sqrt Y else 0 :=
      Finset.sum_le_sum (fun I _ => hb I)
    _ = (F.card : ℝ) * (B * Real.sqrt Y) := by
      rw [Finset.sum_coe_sort S (fun I => if sixthRemainder I = 1 then B * Real.sqrt Y else 0)]
      rw [← Finset.sum_filter]
      simp only [F, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hB (Real.sqrt_nonneg _))

def normalizedIdealAddedZero (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (T : ℝ) : ℂ := (Real.sqrt T : ℂ)⁻¹ * idealAddedZero S hS c

theorem idealAddedZero_energy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (B Y T : ℝ) (hB : 0 ≤ B) (hY : 0 ≤ Y) (hT : 0 < T)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    ‖normalizedIdealAddedZero S hS c T‖ ^ 2 ≤ 16384 * B ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := by
  have hb := idealAddedZero_norm_le S hS c B Y hB hY hc hN
  have hp : (Y ^ (1 / 6 : ℝ)) ^ 2 * Y = Y ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hY]
    norm_num only [Nat.cast_ofNat]
    conv_lhs => rhs; rw [← Real.rpow_one Y]
    rw [← Real.rpow_add' hY (by norm_num : (1 / 3 : ℝ) + 1 ≠ 0)]
    norm_num
  have hs := sq_le_sq₀ (norm_nonneg (idealAddedZero S hS c)) (by positivity : 0 ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y))
  have hb2 := hs.mpr hb
  have hn : ‖normalizedIdealAddedZero S hS c T‖ ^ 2 = T⁻¹ * ‖idealAddedZero S hS c‖ ^ 2 := by
    simp only [normalizedIdealAddedZero, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg T), mul_pow, inv_pow,
      Real.sq_sqrt hT.le]
  rw [hn]
  calc
    T⁻¹ * ‖idealAddedZero S hS c‖ ^ 2 ≤ T⁻¹ * ((128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y)) ^ 2 :=
      mul_le_mul_of_nonneg_left hb2 (inv_nonneg.mpr hT.le)
    _ = 16384 * B ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hY]
      rw [← hp]
      ring

def tupleCoefficient {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (I : Ideal O) : ℂ :=
  ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v

def tupleColumns {r : ℕ} (S : Finset (Fin r → Ideal O)) : Finset (Ideal O) :=
  S.image tupleProduct

lemma tupleColumns_supported {r : ℕ} (S : Finset (Fin r → Ideal O))
    (hS : ∀ v ∈ S, Supported (tupleProduct v)) :
    ∀ I ∈ tupleColumns S, Supported I := by
  intro I hI
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
  exact hS v hv

theorem tupleCoefficient_norm_le {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ v ∈ S, ‖β v‖ ≤ B) (I : Ideal O) (hI : I ≠ 0) :
    ‖tupleCoefficient S β I‖ ≤ B * ((idealDivisors I).card : ℝ) ^ r := by
  calc
    ‖tupleCoefficient S β I‖ ≤ ∑ v ∈ S.filter (fun v => tupleProduct v = I), ‖β v‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _v ∈ S.filter (fun v => tupleProduct v = I), B :=
      Finset.sum_le_sum (fun v hv => hβ v (Finset.mem_filter.mp hv).1)
    _ = B * ((S.filter (fun v => tupleProduct v = I)).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ B * ((idealDivisors I).card : ℝ) ^ r := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast tuple_product_fiber_card S I hI

theorem tuple_added_zero_energy (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Fin r → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v))
      (β : (Fin r → Ideal O) → ℂ) (B Y T : ℝ),
      0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
          (tupleCoefficient S β) T‖ ^ 2 ≤ C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let δ := ε / (2 * r)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hr')
  obtain ⟨D, hD, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨16384 * (D ^ r) ^ 2, by positivity, ?_⟩
  intro S hS β B Y T hB hY hT hβ hN
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hδr : δ * (r : ℝ) = ε / 2 := by dsimp [δ]; field_simp
  have hc (I : Ideal O) (hI : I ∈ tupleColumns S) :
      ‖tupleCoefficient S β I‖ ≤ B * (D ^ r * Y ^ (ε / 2)) := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
    have hI0 := (hS v hv).1
    have hn0 : (0 : ℝ) ≤ Ideal.absNorm (tupleProduct v) := Nat.cast_nonneg _
    calc
      ‖tupleCoefficient S β (tupleProduct v)‖ ≤
          B * ((idealDivisors (tupleProduct v)).card : ℝ) ^ r :=
        tupleCoefficient_norm_le S β B hB hβ _ hI0
      _ ≤ B * (D * (Ideal.absNorm (tupleProduct v) : ℝ) ^ δ) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hI0) _) hB
      _ = B * (D ^ r * (Ideal.absNorm (tupleProduct v) : ℝ) ^ (ε / 2)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hn0, hδr]
      _ ≤ B * (D ^ r * Y ^ (ε / 2)) := by
        gcongr
        exact hN v hv
  have hn (I : Ideal O) (hI : I ∈ tupleColumns S) : (Ideal.absNorm I : ℝ) ≤ Y := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
    exact hN v hv
  have he := idealAddedZero_energy (tupleColumns S) (tupleColumns_supported S hS)
    (tupleCoefficient S β) (B * (D ^ r * Y ^ (ε / 2))) Y T (by positivity) hY0.le hT hc hn
  have hy : (Y ^ (ε / 2)) ^ 2 * Y ^ (4 / 3 : ℝ) = Y ^ (4 / 3 + ε : ℝ) := by
    rw [← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0]
    congr 1
    norm_num
    ring
  calc
    _ ≤ 16384 * (B * (D ^ r * Y ^ (ε / 2))) ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := he
    _ = (16384 * (D ^ r) ^ 2) * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
      rw [← hy]
      ring

def originalCoefficient (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Fin (N + 2) → Ideal O) : ℂ :=
  (∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)) *
    idealWeight c χ R t (tupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
      (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩) *
    (if s ∣ tupleProduct v then 1 else 0)

lemma idealRectangle_norm_le (W₁ W₂ : ℝ → ℂ) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal O) :
    ‖idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J‖ ≤ 2 * B₁ * B₂ := by
  have hprod (x y : ℝ) : ‖W₁ x * W₂ y‖ ≤ B₁ * B₂ := by
    rw [norm_mul]
    exact mul_le_mul (hW₁ x) (hW₂ y) (norm_nonneg _) hB₁
  unfold idealRectangle
  exact (norm_sub_le _ _).trans ((add_le_add
    (hprod ((Ideal.absNorm I : ℝ) / X₁) ((Ideal.absNorm J : ℝ) / X₂))
    (hprod ((Ideal.absNorm I : ℝ) / Y₁) ((Ideal.absNorm J : ℝ) / Y₂))).trans_eq (by ring))

theorem originalCoefficient_norm_le (N : ℕ) (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (Bslot : Fin N → ℝ) (B₁ B₂ : ℝ)
    (hBslot : ∀ j, 0 ≤ Bslot j) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hν : ∀ j I, ‖ν j I‖ ≤ 1) (hWslot : ∀ j x, ‖Wslot j x‖ ≤ Bslot j)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (v : Fin (N + 2) → Ideal O) (hv : tupleProduct v ≠ 0) :
    ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v‖ ≤
      (∏ j, Bslot j) * (2 * B₁ * B₂) := by
  have hslots : ‖∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)‖ ≤ ∏ j, Bslot j := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro j hj
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hν j _) (hWslot j _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hweight := idealWeight_norm_le_one c hc χ R t (tupleProduct v) hv
  have hrect := idealRectangle_norm_le W₁ W₂ B₁ B₂ hB₁ hB₂ hW₁ hW₂ X₁ X₂ Y₁ Y₂
    (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩)
  by_cases hs : s ∣ tupleProduct v
  · simp only [originalCoefficient, hs, ite_true, mul_one, norm_mul]
    have hsw := mul_le_mul hslots hweight (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hBslot j))
    simp only [mul_one] at hsw
    exact mul_le_mul hsw hrect (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hBslot j))
  · simp only [originalCoefficient, hs, ite_false, mul_zero, norm_zero]
    exact mul_nonneg (Finset.prod_nonneg (fun j _ => hBslot j)) (by positivity)

lemma originalCoefficient_eq_zero_of_not_dvd (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (v : Fin (N + 2) → Ideal O) (hs : ¬s ∣ tupleProduct v) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v = 0 := by
  simp only [originalCoefficient, hs, ite_false, mul_zero]

theorem original_added_zero_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : O), c ≠ 0 →
      ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
      (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
      (Bslot : Fin N → ℝ) (B₁ B₂ : ℝ),
      (∀ j, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j I, ‖ν j I‖ ≤ 1) → (∀ j x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Fin (N + 2) → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v)) (Y T : ℝ), 1 ≤ Y → 0 < T →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
        (tupleCoefficient S (originalCoefficient N c χ R t ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ b₁ b₂ s)) T‖ ^ 2 ≤
        C * ((∏ j, Bslot j) * (2 * B₁ * B₂)) ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := tuple_added_zero_energy (N + 2) (by omega) ε hε
  refine ⟨C, hC, ?_⟩
  intro c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Y T hY hT hN
  apply he S hS _ _ Y T (mul_nonneg (Finset.prod_nonneg (fun j _ => hBslot j)) (by positivity)) hY hT _ hN
  intro v hv
  exact originalCoefficient_norm_le N c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s
    Bslot B₁ B₂ hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ v (hS v hv).1

theorem idealAddedZero_eq_gaussPolynomial (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) :
    idealAddedZero S hS c =
      gaussPolynomial (Finset.univ : Finset S)
        (fun I => primaryGenerator I.val)
        (fun I => (supported_span_primaryGenerator_iff I.val).mpr (hS I.val I.property))
        (fun I => c I.val) 0 := rfl

lemma idealGaussRow_zero_divisor_sixth (I : Ideal O) (hI : Supported I)
    (hz : idealGaussRow I hI 0 ≠ 0) (s : Ideal O) (hs : Squarefree s) (hd : s ∣ I) :
    s ^ 6 ∣ I := by
  have hrem := idealGaussRow_zero_sixthRemainder I hI hz
  have he : sixthQuotient I ^ 6 = I := by
    simpa only [hrem, one_mul] using sixth_normal_form I hI.1
  rw [← he] at hd ⊢
  exact pow_dvd_pow_of_dvd ((hs.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp hd) 6

theorem idealAddedZero_nonzero_mask_norm (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (Y : ℝ)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y)
    (hz : idealAddedZero S hS c ≠ 0) : (Ideal.absNorm s : ℝ) ^ 6 ≤ Y := by
  obtain ⟨I, _, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hg : idealGaussRow I.val (hS I.val I.property) 0 ≠ 0 := by
    intro he
    exact hI (by rw [he, mul_zero])
  have hd : s ∣ I.val := by
    by_contra hn
    exact hI (by rw [hmask I.val I.property hn, zero_mul])
  have hpow := idealGaussRow_zero_divisor_sixth I.val (hS I.val I.property) hg s hs hd
  have hn := (norm_le_of_dvd (hS I.val I.property).1 hpow).trans (hN I.val I.property)
  simpa only [map_pow, Nat.cast_pow] using hn

theorem original_tupleCoefficient_mask (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (S : Finset (Fin (N + 2) → Ideal O)) (I : Ideal O) (hs : ¬s ∣ I) :
    tupleCoefficient S (originalCoefficient N c χ R t ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ b₁ b₂ s) I = 0 := by
  apply Finset.sum_eq_zero
  intro v hv
  apply originalCoefficient_eq_zero_of_not_dvd
  rwa [(Finset.mem_filter.mp hv).2]

theorem added_zero_exponent (a s θ : ℝ) (ha : -θ ≤ a) (hs : s ≤ (a + θ) / 6) :
    a / 3 + 4 * θ / 3 ≤ a - s + 2 * θ := by linarith

theorem added_zero_scale_identity (Z a θ : ℝ) (hZ : 0 < Z) :
    (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 : ℝ) = Z ^ (a / 3 + 4 * θ / 3) := by
  rw [← Real.rpow_neg hZ.le, ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ]
  congr 1
  ring

theorem idealAddedZero_source_energy (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (B Z a s θ : ℝ)
    (hB : 0 ≤ B) (hZ : 1 ≤ Z) (ha : -θ ≤ a) (hs : s ≤ (a + θ) / 6)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ)) :
    ‖normalizedIdealAddedZero S hS c (Z ^ a)‖ ^ 2 ≤
      16384 * B ^ 2 * Z ^ (a - s + 2 * θ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have he := idealAddedZero_energy S hS c B (Z ^ (a + θ)) (Z ^ a)
    hB (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hc hN
  calc
    _ ≤ 16384 * B ^ 2 * (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 : ℝ) := he
    _ = 16384 * B ^ 2 * Z ^ (a / 3 + 4 * θ / 3) := by
      rw [mul_assoc, added_zero_scale_identity Z a θ hZ0]
    _ ≤ 16384 * B ^ 2 * Z ^ (a - s + 2 * θ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (added_zero_exponent a s θ ha hs))
        (by positivity)

theorem idealAddedZero_nonzero_mask_dyad (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (Z a s₀ θ : ℝ) (hZ : 1 < Z)
    (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ))
    (hz : idealAddedZero S hS c ≠ 0) : -θ ≤ a ∧ s₀ ≤ (a + θ) / 6 := by
  have hZ0 : 0 < Z := lt_trans zero_lt_one hZ
  obtain ⟨I, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hY : 1 ≤ Z ^ (a + θ) :=
    (norm_one_le (hS I.val I.property).1).trans (hN I.val I.property)
  have ha : 0 ≤ a + θ := (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero] using hY)
  have hm := idealAddedZero_nonzero_mask_norm S hS c s hs hmask (Z ^ (a + θ)) hN hz
  have hp : Z ^ (s₀ * (6 : ℕ)) ≤ Z ^ (a + θ) := by
    rw [Real.rpow_mul_natCast hZ0.le]
    exact (pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) hNs 6).trans hm
  have hsp := (Real.rpow_le_rpow_left_iff hZ).mp hp
  constructor <;> norm_num at hsp ⊢ <;> linarith

theorem idealAddedZero_source_energy_of_mask (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (B Z a s₀ θ : ℝ)
    (hB : 0 ≤ B) (hZ : 1 < Z) (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ)) :
    ‖normalizedIdealAddedZero S hS c (Z ^ a)‖ ^ 2 ≤
      16384 * B ^ 2 * Z ^ (a - s₀ + 2 * θ) := by
  by_cases hz : idealAddedZero S hS c = 0
  · simp only [normalizedIdealAddedZero, hz, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg (by linarith) _)
  · obtain ⟨ha, hss⟩ := idealAddedZero_nonzero_mask_dyad S hS c s hs hmask Z a s₀ θ hZ hNs hN hz
    exact idealAddedZero_source_energy S hS c B Z a s₀ θ hB hZ.le ha hss hc hN

theorem actual_tuple_gauss_eq_columns {r : ℕ} (S : Finset (Fin r → Ideal O))
    (hS : ∀ v ∈ S, Supported (tupleProduct v)) (β : (Fin r → Ideal O) → ℂ) :
    gaussPolynomial (Finset.univ : Finset S)
      (fun v => primaryGenerator (tupleProduct v.val))
      (fun v => (supported_span_primaryGenerator_iff (tupleProduct v.val)).mpr (hS v.val v.property))
      (fun v => β v.val) 0 =
    idealAddedZero (tupleColumns S) (tupleColumns_supported S hS) (tupleCoefficient S β) := by
  let g (I : Ideal O) : ℂ := if hI : Supported I then idealGaussRow I hI 0 else 0
  have hl : gaussPolynomial (Finset.univ : Finset S)
      (fun v => primaryGenerator (tupleProduct v.val))
      (fun v => (supported_span_primaryGenerator_iff (tupleProduct v.val)).mpr (hS v.val v.property))
      (fun v => β v.val) 0 = ∑ v ∈ S, β v * g (tupleProduct v) := by
    rw [← Finset.sum_coe_sort S (fun v => β v * g (tupleProduct v))]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [g, dite_eq_left (hS v.val v.property), idealGaussRow]
  have hr : idealAddedZero (tupleColumns S) (tupleColumns_supported S hS) (tupleCoefficient S β) =
      ∑ I ∈ tupleColumns S, tupleCoefficient S β I * g I := by
    rw [← Finset.sum_coe_sort (tupleColumns S) (fun I => tupleCoefficient S β I * g I)]
    apply Finset.sum_congr rfl
    intro I hI
    simp only [g, dite_eq_left (tupleColumns_supported S hS I.val I.property)]
  rw [hl, hr]
  symm
  simp only [tupleCoefficient, Finset.sum_mul]
  calc
    (∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v * g I) =
        ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v * g (tupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = ∑ v ∈ S, β v * g (tupleProduct v) :=
      Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩) _

end SevenEighths.CenteredMomentAddedZero

end

end OAI

end Source431

/- Original source: OAI/NumberTheory/DirichletL/Moments/AddedZeroUniform.lean; sha256: c0ac095d1be1c3456f4adfee35b5daba5d5ac60ed3a3b68552941470ae5fb62b -/
section Source432
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

theorem uniform_tuple_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ N →
      ∀ (S : Finset (Fin (n + 2) → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v))
      (β : (Fin (n + 2) → Ideal O) → ℂ) (B Y T : ℝ),
      0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
          (tupleCoefficient S β) T‖ ^ 2 ≤ C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  let D (n : ℕ) := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose
  have hD (n : ℕ) : 0 < D n := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose_spec.1
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  let C := 1 + (Finset.range (N + 1)).sup' hne D
  have hzero : D 0 ≤ (Finset.range (N + 1)).sup' hne D :=
    Finset.le_sup' D (by simp : 0 ∈ Finset.range (N + 1))
  refine ⟨C, by dsimp [C]; linarith [hD 0], ?_⟩
  intro n hn S hS β B Y T hB hY hT hβ hN
  have hDn : D n ≤ C := by
    have h := Finset.le_sup' D (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    dsimp only [C]
    linarith
  have he := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose_spec.2
    S hS β B Y T hB hY hT hβ hN
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hT.le)
  exact mul_le_mul_of_nonneg_right hDn (sq_nonneg _)

abbrev Tuple (ι : Type*) := (ι ⊕ Fin 2) → Ideal O

def coordinateEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    ι ⊕ Fin 2 ≃ Fin (n + 2) := (e.sumCongr (Equiv.refl (Fin 2))).trans finSumFinEquiv

def tupleEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    Tuple ι ≃ (Fin (n + 2) → Ideal O) :=
  (coordinateEquiv e).arrowCongr (Equiv.refl (Ideal O))

def finiteTupleProduct {ι : Type*} [Fintype ι] (v : Tuple ι) : Ideal O := ∏ i, v i

lemma tupleEquiv_slot {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (i : ι) :
    tupleEquiv e v ((e i).castAdd 2) = v (Sum.inl i) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inl i) = (e i).castAdd 2 := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, finSumFinEquiv_apply_left]
  rw [← h, Equiv.symm_apply_apply]

lemma tupleEquiv_plain {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (j : Fin 2) :
    tupleEquiv e v (j.natAdd n) = v (Sum.inr j) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inr j) = j.natAdd n := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, finSumFinEquiv_apply_right, Equiv.refl_apply]
  rw [← h, Equiv.symm_apply_apply]

theorem tupleProduct_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (v : Tuple ι) :
    tupleProduct (tupleEquiv e v) = finiteTupleProduct v := by
  exact (coordinateEquiv e).symm.prod_comp v

def originalFiniteCoefficient {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j, ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j)) *
    idealWeight c χ R t (finiteTupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (b₁ * v (Sum.inr 0)) (b₂ * v (Sum.inr 1)) *
    (if s ∣ finiteTupleProduct v then 1 else 0)

theorem originalCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) :
    originalCoefficient n c χ R t (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j))
      (fun j => P (e.symm j)) W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (tupleEquiv e v) =
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v := by
  have hslot (j : Fin n) : tupleEquiv e v (j.castAdd 2) = v (Sum.inl (e.symm j)) := by
    simpa only [Equiv.apply_symm_apply] using tupleEquiv_slot e v (e.symm j)
  have hp₀ : (⟨n, by omega⟩ : Fin (n + 2)) = (0 : Fin 2).natAdd n := by ext; simp
  have hp₁ : (⟨n + 1, by omega⟩ : Fin (n + 2)) = (1 : Fin 2).natAdd n := by ext; simp
  simp only [originalCoefficient, originalFiniteCoefficient, tupleProduct_reindex,
    hslot, hp₀, hp₁, tupleEquiv_plain]
  rw [e.symm.prod_comp (fun j => ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j))]

lemma reindex_supported {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n)
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) :
    ∀ w ∈ S.image (tupleEquiv e), Supported (tupleProduct w) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  rw [tupleProduct_reindex]
  exact hS v hv

def finiteGaussZero {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) (β : Tuple ι → ℂ) : ℂ :=
  gaussPolynomial (Finset.univ : Finset S)
    (fun v => primaryGenerator (finiteTupleProduct v.val))
    (fun v => (supported_span_primaryGenerator_iff (finiteTupleProduct v.val)).mpr (hS v.val v.property))
    (fun v => β v.val) 0

theorem finiteGaussZero_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι))
    (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) (β : Tuple ι → ℂ) :
    finiteGaussZero S hS β =
      idealAddedZero (tupleColumns (S.image (tupleEquiv e)))
        (tupleColumns_supported _ (reindex_supported e S hS))
        (tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w))) := by
  rw [← actual_tuple_gauss_eq_columns (S.image (tupleEquiv e)) (reindex_supported e S hS)
    (fun w => β ((tupleEquiv e).symm w))]
  unfold finiteGaussZero gaussPolynomial
  apply Finset.sum_bij (fun v _ => (⟨tupleEquiv e v.val,
    Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩ : S.image (tupleEquiv e)))
  · intros; exact Finset.mem_univ _
  · intro v hv w hw he
    apply Subtype.ext
    exact (tupleEquiv e).injective (congrArg Subtype.val he)
  · intro w hw
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp w.property
    exact ⟨⟨v, hv⟩, Finset.mem_univ _, Subtype.ext he⟩
  · intro v hv
    simp only [Equiv.symm_apply_apply, tupleProduct_reindex]

theorem uniform_finite_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
      ∀ (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (β : Tuple ι → ℂ) (B Y T : ℝ), 0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) →
      ‖(Real.sqrt T : ℂ)⁻¹ * finiteGaussZero S hS β‖ ^ 2 ≤
        C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := uniform_tuple_energy N ε hε
  refine ⟨C, hC, ?_⟩
  intro ι inst hn S hS β B Y T hB hY hT hβ hN
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β]
  apply he (Fintype.card ι) hn _ (reindex_supported e S hS) _ B Y T hB hY hT
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [Equiv.symm_apply_apply] using hβ v hv
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [tupleProduct_reindex] using hN v hv

theorem originalFiniteCoefficient_norm_le {ι : Type*} [Fintype ι]
    (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (Bslot : ι → ℝ) (B₁ B₂ : ℝ) (hBslot : ∀ j, 0 ≤ Bslot j)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hν : ∀ j I, ‖ν j I‖ ≤ 1) (hWslot : ∀ j x, ‖Wslot j x‖ ≤ Bslot j)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (v : Tuple ι) (hv : finiteTupleProduct v ≠ 0) :
    ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v‖ ≤
      (∏ j, Bslot j) * (2 * B₁ * B₂) := by
  let e := Fintype.equivFin ι
  rw [← originalCoefficient_reindex e]
  have he := originalCoefficient_norm_le (Fintype.card ι) c hc χ R t
    (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j => Bslot (e.symm j)) B₁ B₂
    (fun j => hBslot _) hB₁ hB₂ (fun j I => hν _ I) (fun j x => hWslot _ x) hW₁ hW₂
    (tupleEquiv e v) (by rwa [tupleProduct_reindex])
  simpa only [e.symm.prod_comp Bslot] using he

theorem original_subset_energy {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
      (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Y T : ℝ), 1 ≤ Y → 0 < T →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) →
      ‖(Real.sqrt T : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_energy A.card ε hε
  refine ⟨C, hC, ?_⟩
  intro J hJA c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Y T hY hT hN
  have hcard : Fintype.card J ≤ A.card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hJA
  apply he hcard S hS _ _ Y T
    (mul_nonneg (Finset.prod_nonneg hBslot) (by positivity)) hY hT _ hN
  intro v hv
  have hb := originalFiniteCoefficient_norm_le c hc χ R t
    (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j : J => Bslot j.val) B₁ B₂
    (fun j => hBslot j.val j.property) hB₁ hB₂
    (fun j I => hν j.val j.property I) (fun j x => hWslot j.val j.property x)
    hW₁ hW₂ v (hS v hv).1
  simpa only [Finset.prod_coe_sort J Bslot] using hb

theorem empty_finiteTupleProduct {α : Type*} (v : Tuple (∅ : Finset α)) :
    finiteTupleProduct v = v (Sum.inr 0) * v (Sum.inr 1) := by
  simp only [finiteTupleProduct, Fintype.prod_sum_type, Fin.prod_univ_two]
  have he : (∏ j : (∅ : Finset α), v (Sum.inl j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    exact False.elim (Finset.notMem_empty j.val j.property)
  rw [he, one_mul]

lemma reindexCoefficient_mask {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (s : Ideal O)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (I : Ideal O) (hs : ¬s ∣ I) :
    tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w)) I = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  obtain ⟨hwS, hwI⟩ := Finset.mem_filter.mp hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwS
  simp only [Equiv.symm_apply_apply]
  apply hmask v hv
  rwa [← tupleProduct_reindex e v, hwI]

lemma reindexColumns_norm {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι)) (Y : ℝ)
    (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) :
    ∀ I ∈ tupleColumns (S.image (tupleEquiv e)), (Ideal.absNorm I : ℝ) ≤ Y := by
  intro I hI
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  simpa only [tupleProduct_reindex] using hN v hv

theorem finiteGaussZero_nonzero_mask_norm {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
    (β : Tuple ι → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (Y : ℝ) (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y)
    (hz : finiteGaussZero S hS β ≠ 0) : (Ideal.absNorm s : ℝ) ^ 6 ≤ Y := by
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β] at hz
  exact idealAddedZero_nonzero_mask_norm _ _ _ s hs
    (fun I _ => reindexCoefficient_mask e S β s hmask I) Y (reindexColumns_norm e S Y hN) hz

theorem finiteGaussZero_nonzero_mask_dyad {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
    (β : Tuple ι → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (Z a s₀ θ : ℝ) (hZ : 1 < Z) (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ))
    (hz : finiteGaussZero S hS β ≠ 0) : -θ ≤ a ∧ s₀ ≤ (a + θ) / 6 := by
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β] at hz
  exact idealAddedZero_nonzero_mask_dyad _ _ _ s hs
    (fun I _ => reindexCoefficient_mask e S β s hmask I) Z a s₀ θ hZ hNs
    (reindexColumns_norm e S (Z ^ (a + θ)) hN) hz

lemma originalFiniteCoefficient_mask {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (v : Tuple ι) (hs : ¬s ∣ finiteTupleProduct v) :
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v = 0 := by
  simp only [originalFiniteCoefficient, hs, ite_false, mul_zero]

theorem uniform_finite_source_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
      ∀ (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (β : Tuple ι → ℂ) (s : Ideal O), Squarefree s →
      (∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0) →
      ∀ (B Z a s₀ θ : ℝ), 0 ≤ B → 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS β‖ ^ 2 ≤
        C * B ^ 2 * Z ^ (a - s₀ + 2 * θ + ε * (a + θ)) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_energy N ε hε
  refine ⟨C, hC, ?_⟩
  intro ι inst hn S hS β s hs hmask B Z a s₀ θ hB hZ hNs hβ hN
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  by_cases hz : finiteGaussZero S hS β = 0
  · rw [hz, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) (Real.rpow_nonneg hZ0.le _)
  · obtain ⟨ha, hss⟩ := finiteGaussZero_nonzero_mask_dyad S hS β s hs hmask Z a s₀ θ hZ hNs hN hz
    have hY : 1 ≤ Z ^ (a + θ) := Real.one_le_rpow hZ.le (by linarith)
    have hb := he hn S hS β B (Z ^ (a + θ)) (Z ^ a) hB hY
      (Real.rpow_pos_of_pos hZ0 _) hβ hN
    have hp : (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 + ε : ℝ) =
        Z ^ (a / 3 + 4 * θ / 3 + ε * (a + θ)) := by
      rw [← Real.rpow_neg hZ0.le, ← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]
      congr 1
      ring
    calc
      _ ≤ C * B ^ 2 * (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 + ε : ℝ) := hb
      _ = C * B ^ 2 * Z ^ (a / 3 + 4 * θ / 3 + ε * (a + θ)) := by rw [mul_assoc, hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ.le
          (by linarith [added_zero_exponent a s₀ θ ha hss]))
        (mul_nonneg hC.le (sq_nonneg _))

theorem original_subset_source_energy {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O), Squarefree s →
      ∀ (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Z a s₀ θ : ℝ), 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 *
          Z ^ (a - s₀ + 2 * θ + ε * (a + θ)) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_source_energy A.card ε hε
  refine ⟨C, hC, ?_⟩
  intro J hJA c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s hs Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Z a s₀ θ hZ hNs hN
  have hcard : Fintype.card J ≤ A.card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hJA
  apply he hcard S hS _ s hs
    (fun v _ => originalFiniteCoefficient_mask c χ R t
      (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
      W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v)
    _ Z a s₀ θ (mul_nonneg (Finset.prod_nonneg hBslot) (by positivity)) hZ hNs _ hN
  intro v hv
  have hb := originalFiniteCoefficient_norm_le c hc χ R t
    (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j : J => Bslot j.val) B₁ B₂
    (fun j => hBslot j.val j.property) hB₁ hB₂
    (fun j I => hν j.val j.property I) (fun j x => hWslot j.val j.property x)
    hW₁ hW₂ v (hS v hv).1
  simpa only [Finset.prod_coe_sort J Bslot] using hb

end SevenEighths.CenteredMomentAddedZeroUniform

end

end OAI

end Source432

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceMass.lean; sha256: 0c2fe23aa378e45b59354e53ee11fe41da47d4d70a92e79d04567a68d8826ee9 -/
section Source433
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceMass
open CenteredMomentAddedZero CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => ActualEisensteinCubic.O

def idealBall (H : ℝ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil H)).toFinset.filter
    (fun I => I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H)

@[simp] theorem mem_idealBall (H : ℝ) (I : Ideal O) :
    I ∈ idealBall H ↔ I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_,h⟩
    apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil H)).mem_toFinset.mpr
    exact_mod_cast h.2.trans (Nat.le_ceil H)

lemma idealBall_card (H : ℝ) (hH : 0 ≤ H) :
    ((idealBall H).card : ℝ) ≤ 128*H := by
  by_cases hs : (idealBall H).Nonempty
  · obtain ⟨I,hI⟩ := hs
    have hI := (mem_idealBall H I).mp hI
    have hn : (1:ℝ) ≤ Ideal.absNorm I := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
    exact DescentFiberCost.finite_ideal_count_real _ H (hn.trans hI.2)
      (fun J hJ => ((mem_idealBall H J).mp hJ).1)
      (fun J hJ => ((mem_idealBall H J).mp hJ).2)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

def tupleBox {r : ℕ} (H : Fin r → ℝ) : Finset (Fin r → Ideal O) :=
  Fintype.piFinset (fun i => idealBall (H i))

@[simp] lemma mem_tupleBox {r : ℕ} (H : Fin r → ℝ) (v : Fin r → Ideal O) :
    v ∈ tupleBox H ↔ ∀ i, v i ≠ 0 ∧ (Ideal.absNorm (v i):ℝ) ≤ H i := by
  simp [tupleBox]

lemma tupleBox_card {r : ℕ} (H : Fin r → ℝ) (hH : ∀ i, 0 ≤ H i) :
    ((tupleBox H).card:ℝ) ≤ 128^r * ∏ i, H i := by
  simp only [tupleBox,Fintype.card_piFinset,Nat.cast_prod]
  calc
    (∏ i, ((idealBall (H i)).card:ℝ)) ≤ ∏ i, 128*H i :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => idealBall_card _ (hH i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

def profileProduct {r : ℕ} (W : Fin r → ℝ → ℂ) (q : Fin r → ℝ)
    (v : Fin r → Ideal O) : ℂ := ∏ i, W i ((Ideal.absNorm (v i):ℝ)/q i)

lemma profileProduct_mem_box {r : ℕ} (W : Fin r → ℝ → ℂ) (b q : Fin r → ℝ)
    (hq : ∀ i, 0<q i) (hzero : ∀ i, W i 0=0)
    (hs : ∀ i x, W i x ≠ 0 → x ≤ b i)
    (v : Fin r → Ideal O) (hv : profileProduct W q v ≠ 0) :
    v ∈ tupleBox (fun i => b i*q i) := by
  apply (mem_tupleBox _ _).mpr
  intro i
  have hw : W i ((Ideal.absNorm (v i):ℝ)/q i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hv) i (Finset.mem_univ i)
  refine ⟨?_,(div_le_iff₀ (hq i)).mp (hs i _ hw)⟩
  intro hz
  apply hw
  simp only [hz,map_zero,Nat.cast_zero,zero_div,hzero]

lemma profileProduct_norm_le {r : ℕ} (W : Fin r → ℝ → ℂ) (q B : Fin r → ℝ)
    (hW : ∀ i x, ‖W i x‖ ≤ B i) (v : Fin r → Ideal O) :
    ‖profileProduct W q v‖ ≤ ∏ i, B i := by
  rw [profileProduct,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hW i _)

theorem profileProduct_mass {r : ℕ} (W : Fin r → ℝ → ℂ) (b q B : Fin r → ℝ)
    (hb : ∀ i, 0≤b i) (hq : ∀ i, 0<q i) (hB : ∀ i, 0≤B i)
    (hzero : ∀ i, W i 0=0) (hs : ∀ i x, W i x ≠ 0 → x≤b i)
    (hW : ∀ i x, ‖W i x‖≤B i) (S : Finset (Fin r → Ideal O)) :
    (∑ v ∈ S, ‖profileProduct W q v‖) ≤
      (∏ i, B i) * (128^r * ∏ i, b i*q i) := by
  let F := S.filter (fun v => profileProduct W q v ≠ 0)
  have hsum : (∑ v ∈ S, ‖profileProduct W q v‖) = ∑ v ∈ F, ‖profileProduct W q v‖ := by
    symm
    apply Finset.sum_filter_of_ne
    intro v _ hv
    exact norm_ne_zero_iff.mp hv
  have hsub : F ⊆ tupleBox (fun i => b i*q i) := by
    intro v hv
    exact profileProduct_mem_box W b q hq hzero hs v (Finset.mem_filter.mp hv).2
  have hcard : (F.card:ℝ) ≤ 128^r * ∏ i, b i*q i :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (tupleBox_card _ (fun i => mul_nonneg (hb i) (hq i).le))
  rw [hsum]
  calc
    _ ≤ ∑ _v ∈ F, ∏ i, B i := Finset.sum_le_sum (fun v _ => profileProduct_norm_le W q B hW v)
    _ = (F.card:ℝ)*(∏ i, B i) := by simp
    _ ≤ (128^r * ∏ i, b i*q i)*(∏ i, B i) :=
      mul_le_mul_of_nonneg_right hcard (Finset.prod_nonneg (fun i _ => hB i))
    _ = _ := by ring

def sourceProfiles {N : ℕ} (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) :
    Fin (N+2) → ℝ → ℂ := Fin.append Wslot ![W₁,W₂]

def sourceScales {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) :
    Fin (N+2) → ℝ :=
  Fin.append P ![X₁/(Ideal.absNorm B₁:ℝ),X₂/(Ideal.absNorm B₂:ℝ)]

def sourceBounds {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ) : Fin (N+2) → ℝ :=
  Fin.append b ![b₁,b₂]

lemma sourceProfiles_product {N : ℕ} (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O) :
    profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v =
      (∏ j : Fin N, Wslot j ((Ideal.absNorm (v (j.castAdd 2)):ℝ)/P j)) *
      (W₁ ((Ideal.absNorm (B₁*v ⟨N,by omega⟩):ℝ)/X₁) *
       W₂ ((Ideal.absNorm (B₂*v ⟨N+1,by omega⟩):ℝ)/X₂)) := by
  simp only [profileProduct,Fin.prod_univ_add,sourceProfiles,sourceScales,
    Fin.append_left,Fin.append_right,Fin.prod_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,map_mul,Nat.cast_mul,div_div_eq_mul_div]
  have h₀ : Fin.natAdd N (0:Fin 2)=⟨N,by omega⟩ := by ext; simp
  have h₁ : Fin.natAdd N (1:Fin 2)=⟨N+1,by omega⟩ := by ext; simp
  rw [h₀,h₁]
  congr 2 <;> congr 1 <;> ring

lemma sourceBounds_product {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ) :
    (∏ i, sourceBounds b b₁ b₂ i) = (∏ j,b j)*b₁*b₂ := by
  simp only [sourceBounds,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceScales_product {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∏ i, sourceScales P X₁ X₂ B₁ B₂ i) =
      (∏ j,P j)*(X₁*X₂)/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂) := by
  simp only [sourceScales,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceBounds_nonneg {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ)
    (hb : ∀ j, 0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) :
    ∀ i, 0≤sourceBounds b b₁ b₂ i := by
  simp only [Fin.forall_fin_add,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hb,hb₁,hb₂⟩

lemma sourceScales_pos {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hB₁ : B₁≠0) (hB₂ : B₂≠0) :
    ∀ i, 0<sourceScales P X₁ X₂ B₁ B₂ i := by
  have hn₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  simp only [Fin.forall_fin_add,sourceScales,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hP,div_pos hX₁ hn₁,div_pos hX₂ hn₂⟩

theorem originalCoefficient_factor (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v =
      (∏ j,ν j (v (j.castAdd 2))) * idealWeight c χ R t (tupleProduct v) *
      (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v -
       profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v) *
      (if s∣tupleProduct v then 1 else 0) := by
  rw [originalCoefficient,Finset.prod_mul_distrib,sourceProfiles_product,sourceProfiles_product]
  unfold idealRectangle
  ring

def sourcePool {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) : Finset (Fin (N+2) → Ideal O) :=
  ((tupleBox (fun i => sourceBounds b b₁ b₂ i*sourceScales P X₁ X₂ B₁ B₂ i)) ∪
    tupleBox (fun i => sourceBounds b b₁ b₂ i*sourceScales P Y₁ Y₂ B₁ B₂ i)).filter
      (fun v => ∀ j,ν j (v (j.castAdd 2)) ≠ 0)

lemma sourcePool_slot {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (j : Fin N) :
    ν j (v (j.castAdd 2)) ≠ 0 := (Finset.mem_filter.mp hv).2 j

lemma sourcePool_nonzero {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) : tupleProduct v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with h|h <;>
    exact ((mem_tupleBox _ _).mp h i).1

theorem originalCoefficient_mem_sourcePool (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v ≠ 0) :
    v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [originalCoefficient_factor] at hv
  have hslots := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
  have hd := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  apply Finset.mem_filter.mpr
  refine ⟨?_,fun j => (Finset.prod_ne_zero_iff.mp hslots) j (Finset.mem_univ j)⟩
  apply Finset.mem_union.mpr
  by_cases hx : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v = 0
  · apply Or.inr
    have hy : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v ≠ 0 := by
      intro hy; exact hd (by rw [hx,hy,sub_self])
    exact profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂) hzero hs v hy
  · exact Or.inl (profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂) hzero hs v hx)

def sourceRadius {N : ℕ} (b P : Fin N → ℝ) (b₁ b₂ T : ℝ) (B₁ B₂ : Ideal O) : ℝ :=
  (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)

lemma source_coordinate_product {N : ℕ} (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ T : ℝ) (B₁ B₂ : Ideal O) (hT : X₁*X₂=T) :
    (∏ i,sourceBounds b b₁ b₂ i*sourceScales P X₁ X₂ B₁ B₂ i) =
      sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rw [Finset.prod_mul_distrib,sourceBounds_product,sourceScales_product,hT]
  unfold sourceRadius
  ring

lemma tupleBox_product_bound {r : ℕ} (H : Fin r → ℝ) (v : Fin r → Ideal O)
    (hv : v ∈ tupleBox H) : (Ideal.absNorm (tupleProduct v):ℝ) ≤ ∏ i,H i := by
  simp only [tupleProduct,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
    (fun i _ => ((mem_tupleBox H v).mp hv i).2)

theorem sourcePool_product_bound {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    (Ideal.absNorm (tupleProduct v):ℝ) ≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with hx|hy
  · exact (tupleBox_product_bound _ v hx).trans_eq (source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX)
  · exact (tupleBox_product_bound _ v hy).trans_eq (source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY)

theorem originalCoefficient_profile_norm_le (N : ℕ) (c : O) (hc : c≠0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (hν : ∀ j I, ‖ν j I‖≤1)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : tupleProduct v≠0) :
    ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ ≤
      ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
      ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖ := by
  have hn : ‖∏ j,ν j (v (j.castAdd 2))‖≤1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hν j _)
  have hw := idealWeight_norm_le_one c hc χ R t (tupleProduct v) hv
  rw [originalCoefficient_factor,norm_mul,norm_mul,norm_mul]
  have hm : ‖(if s∣tupleProduct v then 1 else 0 : ℂ)‖≤1 := by split_ifs <;> norm_num
  have hnw : ‖∏ j,ν j (v (j.castAdd 2))‖*‖idealWeight c χ R t (tupleProduct v)‖≤1 := by
    simpa only [one_mul] using mul_le_mul hn hw (norm_nonneg _) zero_le_one
  calc
    _ ≤ (1*‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v-
        profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hnw (norm_nonneg _)) hm (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      simpa only [one_mul,mul_one] using norm_sub_le
        (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v)
        (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v)

def sourceMassConstant {N : ℕ} (b D : Fin N → ℝ) (b₁ b₂ D₁ D₂ : ℝ) : ℝ :=
  2*128^(N+2)*(∏ j,D j)*D₁*D₂*(∏ j,b j)*b₁*b₂

theorem originalCoefficient_mass (N : ℕ) (c : O) (hc : c≠0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (hν : ∀ j I, ‖ν j I‖≤1)
    (Wslot : Fin N → ℝ → ℂ) (P b D : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hb : ∀ j, 0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂)
    (hD : ∀ j, 0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i)
    (hW : ∀ i x, ‖sourceProfiles Wslot W₁ W₂ i x‖≤sourceBounds D D₁ D₂ i)
    (S : Finset (Fin (N+2) → Ideal O)) :
    (∑ v ∈ S, ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
      sourceMassConstant b D b₁ b₂ D₁ D₂ *
        (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  have hpoint (v : Fin (N+2) → Ideal O) :
      ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ ≤
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖ := by
    by_cases hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=0
    · rw [hv,norm_zero]; positivity
    · have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
      exact originalCoefficient_profile_norm_le N c hc χ R t ν hν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ s v (sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm)
  have hx := profileProduct_mass (sourceProfiles Wslot W₁ W₂) (sourceBounds b b₁ b₂)
    (sourceScales P X₁ X₂ B₁ B₂) (sourceBounds D D₁ D₂)
    (sourceBounds_nonneg b b₁ b₂ hb hb₁ hb₂) (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂)
    (sourceBounds_nonneg D D₁ D₂ hD hD₁ hD₂) hzero hs hW S
  have hy := profileProduct_mass (sourceProfiles Wslot W₁ W₂) (sourceBounds b b₁ b₂)
    (sourceScales P Y₁ Y₂ B₁ B₂) (sourceBounds D D₁ D₂)
    (sourceBounds_nonneg b b₁ b₂ hb hb₁ hb₂) (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂)
    (sourceBounds_nonneg D D₁ D₂ hD hD₁ hD₂) hzero hs hW S
  rw [source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX,sourceBounds_product] at hx
  rw [source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY,sourceBounds_product] at hy
  calc
    _ ≤ ∑ v ∈ S, (‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖) :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact (add_le_add hx hy).trans_eq (by unfold sourceRadius sourceMassConstant; ring)

theorem sourcePool_original_slots {N : ℕ} (ν : Fin N → Ideal O → ℂ)
    (pool : Fin N → Finset (Ideal O)) (hpool : ∀ j I, I∉pool j → ν j I=0)
    (b P : Fin N → ℝ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (v : Fin (N+2) → Ideal O) (hv : v∈sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    ∀ j, v (j.castAdd 2)∈pool j := by
  intro j
  by_contra h
  exact sourcePool_slot _ _ _ _ _ _ _ _ _ _ _ v hv j (hpool j _ h)

theorem tuple_weighted_regroup {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (F : Ideal O → ℂ) :
    (∑ v ∈ S, β v*F (tupleProduct v)) =
      ∑ I ∈ tupleColumns S, tupleCoefficient S β I*F I := by
  symm
  simp only [tupleCoefficient,Finset.sum_mul]
  calc
    _ = ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v=I), β v*F (tupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

theorem tupleCoefficient_mass {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) :
    (∑ I ∈ tupleColumns S, ‖tupleCoefficient S β I‖) ≤ ∑ v ∈ S, ‖β v‖ := by
  calc
    _ ≤ ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v=I), ‖β v‖ :=
      Finset.sum_le_sum (fun I _ => norm_sum_le _ _)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

lemma tupleCoefficient_eq_zero_outside {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (I : Ideal O) (hI : I∉tupleColumns S) :
    tupleCoefficient S β I=0 := by
  apply Finset.sum_eq_zero
  intro v hv
  exact False.elim (hI (Finset.mem_image.mpr ⟨v,(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2⟩))

theorem source_column_support {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (β : (Fin (N+2) → Ideal O) → ℂ) (I : Ideal O)
    (hI : tupleCoefficient (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) β I ≠ 0) :
    I≠0 ∧ (Ideal.absNorm I:ℝ)≤sourceRadius b P b₁ b₂ T B₁ B₂ := by
  have hm : I∈tupleColumns (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) := by
    by_contra h; exact hI (tupleCoefficient_eq_zero_outside _ _ _ h)
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
  exact ⟨sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hv,
    sourcePool_product_bound _ _ _ _ _ _ _ _ _ _ _ _ hX hY v hv⟩

theorem original_source_eq_columns (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i)
    (F : Ideal O → ℂ) :
    (∑' v : Fin (N+2) → Ideal O,
      originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v * F (tupleProduct v)) =
    ∑ I ∈ tupleColumns (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂),
      tupleCoefficient (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
        (originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I * F I := by
  rw [← tuple_weighted_regroup]
  apply tsum_eq_sum
  intro v hv
  have hz : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v = 0 := by
    by_contra hn
    exact hv (originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hn)
  rw [hz,zero_mul]

lemma smooth_annular_bound (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ D : ℝ, 0≤D ∧ (∀ x, ‖W x‖≤D) ∧ W 0=0 ∧ (∀ x, W x≠0 → x≤b) := by
  let D := SchwartzMap.seminorm ℝ 0 0 (CenteredMomentLattice.normPowerProfile W a b ha hs hW 0)
  refine ⟨D,apply_nonneg _ _,?_,?_,?_⟩
  · intro x
    rw [← CenteredMomentTwist.normPowerProfile_norm W a b ha hs hW 0 x]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  · by_contra hz
    have h := (hs hz).1
    linarith
  · intro x hx
    exact (hs hx).2

theorem smooth_source_mass_uniform (N : ℕ)
    (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : Fin N → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0<a j) (hb : ∀ j, 0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0<C ∧ ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ), (∀ j I, ‖ν j I‖≤1) →
      ∀ (P : Fin N → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j, 0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Fin (N+2) → Ideal O),
      (∑ v ∈ S, ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) ∧
      (∑ I ∈ tupleColumns S, ‖tupleCoefficient S
        (originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  choose D hD hDbound hDzero hDsupport using
    fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDbound₁,hzero₁,hsupport₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDbound₂,hzero₂,hsupport₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  have hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDzero (And.intro hzero₁ hzero₂)
  have hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDsupport (And.intro hsupport₁ hsupport₂)
  have hbound : ∀ i x, ‖sourceProfiles Wslot W₁ W₂ i x‖≤sourceBounds D D₁ D₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDbound (And.intro hDbound₁ hDbound₂)
  let C₀ := sourceMassConstant b D b₁ b₂ D₁ D₂
  have hprodD : 0≤∏ j,D j := Finset.prod_nonneg (fun j _ => hD j)
  have hprodb : 0≤∏ j,b j := Finset.prod_nonneg (fun j _ => hb j)
  have hC₀ : 0≤C₀ := by
    dsimp only [C₀,sourceMassConstant]
    positivity
  refine ⟨1+C₀,by positivity,?_⟩
  intro c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hm := originalCoefficient_mass N c hc χ R t ν hν Wslot P b D W₁ W₂
    b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s hb hb₁ hb₂ hD hD₁ hD₂
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hs hbound S
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏ j,P j := Finset.prod_nonneg (fun j _ => (hP j).le)
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by positivity
  have hbigger : C₀*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) ≤
      (1+C₀)*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (by linarith : C₀≤1+C₀) hraw
  have hmass := hm.trans hbigger
  exact ⟨hmass,(tupleCoefficient_mass S _).trans hmass⟩

theorem originalCoefficient_original_masks (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    IsCoprime (tupleProduct v) R ∧ s∣tupleProduct v ∧ ∀ j, ν j (v (j.castAdd 2))≠0 := by
  refine ⟨?_,?_,?_⟩
  · by_contra h
    apply hv
    simp only [originalCoefficient,idealWeight,h,ite_false,zero_mul,mul_zero]
  · by_contra h
    apply hv
    simp only [originalCoefficient,h,ite_false,mul_zero]
  · rw [originalCoefficient_factor] at hv
    have hslots := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
    exact fun j => (Finset.prod_ne_zero_iff.mp hslots) j (Finset.mem_univ j)

theorem originalCoefficient_product_bound (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    tupleProduct v≠0 ∧ (Ideal.absNorm (tupleProduct v):ℝ)≤sourceRadius b P b₁ b₂ T B₁ B₂ := by
  have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
  exact ⟨sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm,
    sourcePool_product_bound _ _ _ _ _ _ _ _ _ _ _ _ hX hY v hm⟩

theorem sourceProfiles_annular_support (N : ℕ) (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : Fin N → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0<a j) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) :
    (∀ i, sourceProfiles Wslot W₁ W₂ i 0=0) ∧
    (∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤sourceBounds b b₁ b₂ i) := by
  have hz (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
    by_contra h
    have h' := (hs h).1
    linarith
  constructor
  · simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,Fin.forall_fin_two,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hz (Wslot j) (a j) (b j) (ha j) (hsSlot j))
        (And.intro (hz W₁ a₁ b₁ ha₁ hs₁) (hz W₂ a₂ b₂ ha₂ hs₂))
  · simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j x (hx : Wslot j x≠0) => (hsSlot j hx).2)
        (And.intro (fun x (hx : W₁ x≠0) => (hs₁ hx).2) (fun x (hx : W₂ x≠0) => (hs₂ hx).2))

theorem sourcePool_prime_slots {N : ℕ} (ν : Fin N → Ideal O → ℂ)
    (pool : Fin N → Finset (Ideal O)) (hpool : ∀ j I, I∉pool j → ν j I=0)
    (hprime : ∀ j I, I∈pool j → Prime I)
    (hdisjoint : Pairwise (Function.onFun Disjoint pool))
    (b P : Fin N → ℝ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (v : Fin (N+2) → Ideal O) (hv : v∈sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    (∀ j : Fin N, Prime (v (j.castAdd 2))) ∧ Function.Injective (fun j : Fin N => v (j.castAdd 2)) := by
  have hm := sourcePool_original_slots ν pool hpool b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v hv
  refine ⟨fun j => hprime j _ (hm j),?_⟩
  intro i j he
  by_contra hij
  have hmj : v (i.castAdd 2)∈pool j := by
    rw [show v (i.castAdd 2)=v (j.castAdd 2) from he]
    exact hm j
  exact Finset.disjoint_left.mp (hdisjoint hij) (hm i) hmj

open CenteredMomentAddedZeroUniform

def finiteColumns {ι : Type*} [Fintype ι] (S : Finset (Tuple ι)) : Finset (Ideal O) :=
  S.image finiteTupleProduct

def finiteColumnCoefficient {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) (I : Ideal O) : ℂ :=
  ∑ v ∈ S.filter (fun v => finiteTupleProduct v=I), β v

lemma finiteColumnCoefficient_mass {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) :
    (∑ I ∈ finiteColumns S, ‖finiteColumnCoefficient S β I‖) ≤ ∑ v ∈ S, ‖β v‖ := by
  calc
    _ ≤ ∑ I ∈ finiteColumns S, ∑ v ∈ S.filter (fun v => finiteTupleProduct v=I), ‖β v‖ :=
      Finset.sum_le_sum (fun I _ => norm_sum_le _ _)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

lemma finite_original_mass_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (S : Finset (Tuple ι)) :
    (∑ v ∈ S.image (tupleEquiv e), ‖originalCoefficient n c χ R t
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) =
    ∑ v ∈ S, ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ := by
  rw [Finset.sum_image (fun v _ w _ he => (tupleEquiv e).injective he)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [originalCoefficient_reindex]

theorem smooth_finite_source_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0<a j) (hb : ∀ j, 0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0<C ∧ ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ), (∀ j I, ‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j, 0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      (∑ v ∈ S, ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  let e := Fintype.equivFin ι
  obtain ⟨C,hC,hbound⟩ := smooth_source_mass_uniform (Fintype.card ι)
    (fun j => Wslot (e.symm j)) W₁ W₂ (fun j => a (e.symm j)) (fun j => b (e.symm j))
    a₁ b₁ a₂ b₂ (fun j => ha _) (fun j => hb _) ha₁ hb₁ ha₂ hb₂
    (fun j => hsSlot _) hs₁ hs₂ (fun j => hWslot _) hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hm := (hbound c hc χ R t (fun j => ν (e.symm j)) (fun j I => hν _ I)
    (fun j => P (e.symm j)) X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP _)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY (S.image (tupleEquiv e))).1
  rw [finite_original_mass_reindex] at hm
  simpa only [e.symm.prod_comp P] using hm

theorem smooth_subset_source_mass_uniform {α : Type*} (A : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈A, 0<a j) (hb : ∀ j∈A, 0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈A, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈A, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0<C ∧ ∀ J : Finset α, J⊆A →
      ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ), (∀ j∈J, ∀ I, ‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J, 0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple J),
      (∑ v ∈ S, ‖originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
        (fun j : J => Wslot j.val) (fun j : J => P j.val)
        W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) ∧
      (∑ I ∈ finiteColumns S, ‖finiteColumnCoefficient S
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) := by
  have hfamily (J : Finset α) (hJ : J⊆A) := smooth_finite_source_mass_uniform
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂
  let D (J : Finset α) : ℝ := if hJ : J⊆A then (hfamily J hJ).choose else 1
  have hD (J : Finset α) : 0<D J := by
    dsimp only [D]
    split_ifs with hJ
    · exact (hfamily J hJ).choose_spec.1
    · norm_num
  let C := 1+∑ J∈A.powerset,D J
  have hsum : 0≤∑ J∈A.powerset,D J := Finset.sum_nonneg (fun J _ => (hD J).le)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro J hJ c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hDC : D J≤C := by
    have hle := Finset.single_le_sum (fun K _ => (hD K).le) (Finset.mem_powerset.mpr hJ)
    dsimp only [C]
    linarith
  have hm := (hfamily J hJ).choose_spec.2 c hc χ R t (fun j : J => ν j.val)
    (fun j I => hν j.val j.property I) (fun j : J => P j.val)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have he : D J=(hfamily J hJ).choose := by simp only [D,dite_eq_left hJ]
  rw [← he,Finset.prod_coe_sort] at hm
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏ j∈J,P j := Finset.prod_nonneg (fun j hj => (hP j hj).le)
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) := by positivity
  have hm' := hm.trans (show D J*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) ≤
      C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) from
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hDC hraw)
  exact ⟨hm',(finiteColumnCoefficient_mass S _).trans hm'⟩

theorem finiteColumns_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (S : Finset (Tuple ι)) :
    tupleColumns (S.image (tupleEquiv e))=finiteColumns S := by
  simp only [tupleColumns,finiteColumns,Finset.image_image]
  congr 1
  funext v
  exact tupleProduct_reindex e v

theorem finiteColumnCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O) :
    tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w)) I =
      finiteColumnCoefficient S β I := by
  unfold tupleCoefficient finiteColumnCoefficient
  have hset : (S.image (tupleEquiv e)).filter (fun w => tupleProduct w=I) =
      (S.filter (fun v => finiteTupleProduct v=I)).image (tupleEquiv e) := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨v,hv,rfl⟩,hprod⟩
      exact ⟨v,⟨hv,by simpa only [tupleProduct_reindex] using hprod⟩,rfl⟩
    · rintro ⟨v,⟨hv,hprod⟩,rfl⟩
      exact ⟨⟨v,hv,rfl⟩,by simpa only [tupleProduct_reindex] using hprod⟩
  rw [hset,Finset.sum_image (fun v _ w _ he => (tupleEquiv e).injective he)]
  simp only [Equiv.symm_apply_apply]

end SevenEighths.CenteredMomentSourceMass

end

end OAI

end Source433

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceProfileMass.lean; sha256: 6bc7a7f76d8ccb7dd9d6ba6e7b49f72810afd83285f58cb3de5a90a4f6d95275 -/
section Source434
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceProfileMass
open ActualEisensteinCubic CenteredMomentPrimary CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
local notation "O" => ActualEisensteinCubic.O

 theorem primary_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (I : Ideal O) :
    primaryIdealCharacter 1 χ I=1 := by
  rw [primaryIdealCharacter_apply]
  have he : Ideal.Quotient.mk (Ideal.span {(1:O)}) (CompletedGauss.primaryGenerator I)=1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(1:O)}))]
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.span_singleton_one]
    trivial
  rw [he,map_one]

 theorem idealWeight_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (R I : Ideal O) :
    CenteredMomentRectangle.idealWeight 1 χ R 0 I=(if IsCoprime I R then 1 else 0) := by
  simp only [idealWeight,primary_mod_one,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]

def profileCoefficient {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))*
    (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))*
    (if s∣finiteTupleProduct v then 1 else 0)

 theorem profileCoefficient_eq_original {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      originalFiniteCoefficient 1 (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  rw [originalFiniteCoefficient,idealWeight_mod_one]
  rfl

theorem profile_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Ideal O) (ν : ι → Ideal O → ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      (∑ v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  obtain ⟨C,hC,ht⟩ := smooth_finite_source_mass_uniform Wslot W₁ W₂ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  simp_rw [profileCoefficient_eq_original]
  exact ht 1 one_ne_zero 1 R 0 ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S

end SevenEighths.CenteredMomentSourceProfileMass

end

end OAI

end Source434

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonProfile.lean; sha256: f18b6eea1fe2ba9e9482f8d0d0b511f1aa29775e944c75ed84d9bc233a09ad3a -/
section Source435
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonProfile
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonPrimeSlots CenteredMomentCommonAllocationBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def liveIndices (B : Tuple ι) : Finset ι := Finset.univ.filter (fun i => B (Sum.inl i)=1)

def remainingTuple (B u : Tuple ι) : Tuple (liveIndices B) :=
  Sum.elim (fun i => u (Sum.inl i.val)) (fun j => u (Sum.inr j))

@[simp] theorem remainingTuple_slot (B u : Tuple ι) (i : liveIndices B) :
    remainingTuple B u (Sum.inl i)=u (Sum.inl i.val) := rfl

@[simp] theorem remainingTuple_plain (B u : Tuple ι) (j : Fin 2) :
    remainingTuple B u (Sum.inr j)=u (Sum.inr j) := rfl

theorem remaining_product (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    finiteTupleProduct u=finiteTupleProduct (remainingTuple B u) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,remainingTuple,
    Sum.elim_inl,Sum.elim_inr]
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => u (Sum.inl i))]
  congr 1
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hnot
  apply hf i
  intro hBi
  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBi⟩)

theorem slot_profiles_split (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (β : ι → Ideal O → ℂ) :
    (∏ i,β i (B (Sum.inl i)*u (Sum.inl i)))=
      (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),β i (B (Sum.inl i)))*
        ∏ i : liveIndices B,β i.val (u (Sum.inl i.val)) := by
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => β i (u (Sum.inl i)))]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1)
    (fun i => β i (B (Sum.inl i)*u (Sum.inl i))),mul_comm]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hf i (Finset.mem_filter.mp hi).2,mul_one]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2,one_mul]

theorem profile_common_allocation (B u : Tuple ι) (C R s : Ideal O)
    (hB : finiteTupleProduct B=C) (hsC : s∣C)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)=
      ((∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0))*
        profileCoefficient R (fun i : liveIndices B => ν i.val) (fun i => Wslot i.val) (fun i => P i.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 (remainingTuple B u) := by
  have hprod : finiteTupleProduct (fun i => B i*u i)=C*finiteTupleProduct (remainingTuple B u) := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct u=_
    rw [hB,remaining_product B u hf]
  have hdiv : s∣C*finiteTupleProduct (remainingTuple B u) := dvd_mul_of_dvd_left hsC _
  unfold profileCoefficient
  rw [slot_profiles_split B u hf (fun i I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)),hprod]
  simp only [hdiv,ite_true,one_dvd,mul_one,remainingTuple_slot,remainingTuple_plain,
    IsCoprime.mul_left_iff]
  rw [mul_assoc B₁,mul_assoc B₂]
  by_cases hC : IsCoprime C R <;>
    by_cases hu : IsCoprime (finiteTupleProduct (remainingTuple B u)) R <;>
    simp_all only [true_and,false_and,ite_true,ite_false,mul_zero,zero_mul,mul_one]
  ring

theorem actual_frozen_slots (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : Tuple ι) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,IdealMobiusDivisorSum.primeSupport (B i)⊆IdealMobiusDivisorSum.primeSupport C)
    (u : Tuple ι) (hu : u∈residualBoxes S C B hB)
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) :
    ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 := by
  intro i hi
  rcases prime_coordinate_cases S hS C hC B hB hBs u hu (Sum.inl i) (hp i) with h|h
  · exact False.elim (hi h.1)
  · exact h.1

end SevenEighths.CenteredMomentCommonProfile

end

end OAI

end Source435

/- Original source: OAI/NumberTheory/DirichletL/Moments/RemainingBox.lean; sha256: 2527c5d68819298a89be08d9f904362748785e5f930ed84c7756f99bccb8cf8f -/
section Source436
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentRemainingBox
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def restoreTuple (B : Tuple ι) (v : Tuple (liveIndices B)) : Tuple ι :=
  Sum.elim (fun i => if h : i∈liveIndices B then v (Sum.inl ⟨i,h⟩) else 1)
    (fun j => v (Sum.inr j))

@[simp] theorem remaining_restore (B : Tuple ι) (v : Tuple (liveIndices B)) :
    remainingTuple B (restoreTuple B v)=v := by
  funext i
  rcases i with i|j
  · simp [remainingTuple,restoreTuple]
  · rfl

theorem restore_remaining (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    restoreTuple B (remainingTuple B u)=u := by
  funext i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · rfl
    · exact (hf i (by simpa [liveIndices] using hi)).symm
  · rfl

def remainingSets (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O)) :
    (liveIndices B ⊕ Fin 2) → Finset (Ideal O) :=
  Sum.elim (fun i => S (Sum.inl i.val)) (fun j => S (Sum.inr j))

theorem remaining_mem (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (u : Tuple ι) (hu : u∈Fintype.piFinset S) :
    remainingTuple B u∈Fintype.piFinset (remainingSets B S) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · exact Fintype.mem_piFinset.mp hu (Sum.inl i.val)
  · exact Fintype.mem_piFinset.mp hu (Sum.inr j)

theorem restore_mem (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hg : ∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i))
    (v : Tuple (liveIndices B)) (hv : v∈Fintype.piFinset (remainingSets B S)) :
    restoreTuple B v∈Fintype.piFinset S := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · exact Fintype.mem_piFinset.mp hv (Sum.inl ⟨i,hi⟩)
    · exact hg i (by simpa [liveIndices] using hi)
  · exact Fintype.mem_piFinset.mp hv (Sum.inr j)

theorem remaining_box_sum (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hf : ∀ i,B (Sum.inl i)≠1 → ∀ I∈S (Sum.inl i),I=1)
    (hg : ∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i))
    (F : Tuple ι → ℂ) :
    (∑ u∈Fintype.piFinset S,F u)=
      ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) := by
  apply Finset.sum_bij (fun u _ => remainingTuple B u)
  · exact fun u hu => remaining_mem B S u hu
  · intro u hu v hv he
    have hu' := restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))
    have hv' := restore_remaining B v (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hv _))
    rw [← hu',← hv',he]
  · intro v hv
    exact ⟨restoreTuple B v,restore_mem B S hg v hv,remaining_restore B v⟩
  · intro u hu
    rw [restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))]

theorem remaining_box_sum_gate (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hf : ∀ i,B (Sum.inl i)≠1 → ∀ I∈S (Sum.inl i),I=1)
    (F : Tuple ι → ℂ) :
    (∑ u∈Fintype.piFinset S,F u)=
      if (∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i)) then
        ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) else 0 := by
  split_ifs with hg
  · exact remaining_box_sum B S hf hg F
  · have he : Fintype.piFinset S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      apply hg
      intro i hi
      have hui := Fintype.mem_piFinset.mp hu (Sum.inl i)
      rwa [hf i hi _ hui] at hui
    rw [he,Finset.sum_empty]

end SevenEighths.CenteredMomentRemainingBox

end

end OAI

end Source436

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonPuncture.lean; sha256: 0a0626cf48c4fad5d299bf98147e00c2c5708285a29318144c94633750a7549a -/
section Source437
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonPuncture
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O

 theorem residualBoxes_filter {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0) :
    residualBoxes S C B hB=
      (Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i))).filter
        (fun u => IsCoprime C (∏ i,u i)) := by
  ext u
  simp only [residualBoxes,Fintype.mem_piFinset,Finset.mem_filter,
    IsCoprime.prod_right_iff,Finset.mem_univ,forall_const]
  exact forall_and

theorem residualBoxes_sum {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (F : (ι → Ideal O) → ℂ) :
    (∑ u∈residualBoxes S C B hB,F u)=
      ∑ u∈Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i)),
        (if IsCoprime C (∏ i,u i) then 1 else 0)*F u := by
  rw [residualBoxes_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs <;> simp

theorem profileCoefficient_puncture {ι : Type*} [Fintype ι]
    (C R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    (if IsCoprime C (finiteTupleProduct v) then 1 else 0)*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  unfold profileCoefficient
  rw [IsCoprime.mul_right_iff,show IsCoprime C (finiteTupleProduct v) ↔ IsCoprime (finiteTupleProduct v) C from isCoprime_comm]
  by_cases hC : IsCoprime (finiteTupleProduct v) C <;>
    by_cases hR : IsCoprime (finiteTupleProduct v) R <;> simp [hC,hR]

theorem residual_profile_sum {ι : Type*} [Fintype ι]
    (S : (ι ⊕ Fin 2) → Finset (Ideal O)) (C : Ideal O) (B : Tuple ι) (hB : ∀ i,B i≠0)
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (F : Tuple ι → ℂ) :
    (∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u*F u)=
      ∑ u∈Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i)),
        profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u*F u := by
  have he (u : Tuple ι) :
      (if IsCoprime C (∏ i,u i) then 1 else 0)*
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u=
        profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u :=
    profileCoefficient_puncture C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u
  rw [residualBoxes_sum]
  simp_rw [← mul_assoc,he]
  apply Finset.sum_congr
  · ext u
    simp only [Fintype.mem_piFinset]
  · intro u hu
    rfl

end SevenEighths.CenteredMomentCommonPuncture

end

end OAI

end Source437

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceLiveAllocation.lean; sha256: 184906477cd86d7305b00e27db8842b4d565ff846e96fdbd9b480a0b35b2fa50 -/
section Source438
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceLiveAllocation
open CenteredMomentRemainingBox CenteredMomentCommonProfile CenteredMomentCommonPuncture
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem prime_residual_frozen (B : Tuple ι) (hB : ∀ i,B i≠0)
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) :
    ∀ i,B (Sum.inl i)≠1 → ∀ I∈residualPool (B (Sum.inl i)) (hB _) (S (Sum.inl i)),I=1 := by
  intro i hi I hI
  have hprime := hp i _ ((mem_residualPool _ _ _ _).mp hI)
  rcases hprime.irreducible.isUnit_or_isUnit rfl with h|h
  · exact False.elim (hi (by simpa only [Ideal.isUnit_iff,Ideal.one_eq_top] using h))
  · simpa only [Ideal.isUnit_iff,Ideal.one_eq_top] using h

theorem allocation_frozen_gate (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) (C : Ideal O) (B : Tuple ι)
    (hB : B∈CenteredMomentCommonAllocationSum.allocationLabels S C) :
    ∀ i,B (Sum.inl i)≠1 → B (Sum.inl i)∈S (Sum.inl i) := by
  classical
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hB
  intro i hi
  have hvi : v (Sum.inl i)∈S (Sum.inl i) := by
    have hh := hv
    simp only [Fintype.mem_piFinset] at hh
    exact hh (Sum.inl i)
  have he := congrFun hvB (Sum.inl i)
  change CenteredMomentSupport.supportExtract (v (Sum.inl i))
    (IdealMobiusDivisorSum.primeSupport C)=B (Sum.inl i) at he
  rw [CenteredMomentSupport.supportExtract_prime _ (hp i _ hvi)] at he
  split_ifs at he with hm
  · rwa [he] at hvi
  · exact False.elim (hi he.symm)

theorem live_residual_pool (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (B : Tuple ι) (hB : ∀ i,B i≠0) (i : liveIndices B) :
    residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val))=S (Sum.inl i.val) := by
  ext I
  rw [mem_residualPool,(Finset.mem_filter.mp i.property).2,one_mul]

theorem residual_source_profile (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s : Ideal O)
    (hprod : finiteTupleProduct B=C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (F : Tuple (liveIndices B) → ℂ) :
    (∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)*
        F (remainingTuple B u))=
      ((∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0))*
      (if (∀ i,B (Sum.inl i)≠1 → B (Sum.inl i)∈S (Sum.inl i)) then
        ∑ v∈Fintype.piFinset (remainingSets B (fun i => residualPool (B i) (hB i) (S i))),
          profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
            (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
            (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v*F v else 0) := by
  let T := fun i => residualPool (B i) (hB i) (S i)
  have hf := prime_residual_frozen B hB S hp
  let A := (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0)
  let G := fun v : Tuple (liveIndices B) =>
    profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
      (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
      (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v*F v
  rw [residualBoxes_sum]
  calc
    _ = ∑ u∈Fintype.piFinset T,A*G (remainingTuple B u) := by
      apply Finset.sum_congr
      · ext u;simp only [Fintype.mem_piFinset];rfl
      · intro u hu
        have hfu : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 :=
          fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _)
        rw [profile_common_allocation B u C R s hprod hsC hfu]
        change (if IsCoprime C (finiteTupleProduct u) then 1 else 0)*
          (A*_ * F (remainingTuple B u))=_
        rw [remaining_product B u hfu]
        dsimp only [G]
        rw [← profileCoefficient_puncture C R]
        ring
    _ = A*(∑ u∈Fintype.piFinset T,G (remainingTuple B u)) := by rw [Finset.mul_sum]
    _ = _ := by
      rw [remaining_box_sum_gate B T hf]
      simp only [remaining_restore,T,mem_residualPool,mul_one]
      rfl

end SevenEighths.CenteredMomentSourceLiveAllocation

end

end OAI

end Source438

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceLiveColumn.lean; sha256: aec066f684433cf9a258023b9102d49023bc15a1738668c0149a7413a2ffab18 -/
section Source439
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceLiveColumn
open CenteredMomentSourceLiveAllocation CenteredMomentRemainingBox CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationBox CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def frozenCoefficient (B : Tuple ι) (C R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) : ℂ :=
  (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
    ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
    (if IsCoprime C R then 1 else 0)

def liveBox (S : (ι ⊕ Fin 2) → Finset (Ideal O)) (B : Tuple ι) (hB : ∀ i,B i≠0) :
    Finset (Tuple (liveIndices B)) :=
  Fintype.piFinset (remainingSets B (fun i => residualPool (B i) (hB i) (S i)))

def liveProfile (B : Tuple ι) (C R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    Tuple (liveIndices B) → ℂ :=
  profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1

theorem residual_source_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s a : Ideal O)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∑ u∈residualBoxes S C B hB,if finiteTupleProduct u=a then
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i) else 0)=
      frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B hB)
          (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  have hh := residual_source_profile S hp B hB C R s hprod hsC ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (fun v => if finiteTupleProduct v=a then 1 else 0)
  rw [ite_eq_left (allocation_frozen_gate S hp C B hlabel)] at hh
  calc
    _ = ∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)*
        (if finiteTupleProduct (remainingTuple B u)=a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 := by
        intro i hi
        have hui := hu
        simp only [residualBoxes,Fintype.mem_piFinset] at hui
        exact prime_residual_frozen B hB S hp i hi _
          (Finset.mem_filter.mp (hui (Sum.inl i))).1
      rw [remaining_product B u hf]
      split_ifs <;> simp
    _ = _ := hh.trans (by
      unfold frozenCoefficient finiteColumnCoefficient liveBox liveProfile
      rw [Finset.sum_filter]
      congr 1
      apply Finset.sum_congr
      · ext v;simp only [Fintype.mem_piFinset]
      intro v hv
      split_ifs <;> simp)

theorem original_source_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s a : Ideal O) (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*a)=
      ∑ B : actualAllocations S C,
        frozenCoefficient B C R ν Wslot P*
          finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
            (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  simp only [finiteColumnCoefficient, Finset.sum_filter]
  have halloc := original_coefficient_allocated S hS C a hC ha hCa
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  change (∑ v ∈ Fintype.piFinset S, if finiteTupleProduct v = C * a then
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v else 0) = _ at halloc
  rw [halloc]
  apply Finset.sum_congr rfl
  intro B hB
  have h := residual_source_column S hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R s a
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2 hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  simp only [finiteColumnCoefficient, Finset.sum_filter] at h
  exact h

end SevenEighths.CenteredMomentSourceLiveColumn

end

end OAI

end Source439
