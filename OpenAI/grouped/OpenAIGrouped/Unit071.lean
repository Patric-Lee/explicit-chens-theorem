import OpenAIGrouped.Unit070
import OpenAIGrouped.Unit066
import OpenAIGrouped.Unit059
import OpenAIGrouped.Unit058
import OpenAIGrouped.Unit060
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit052
import OpenAIGrouped.Unit046
import OpenAIGrouped.Unit018
import OpenAIGrouped.Unit033
import OpenAIGrouped.Unit045
import OpenAIGrouped.Unit032

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerPool.lean; sha256: cf9f3111f49854a66e74b18aa0fa8404a3ee3e72fee23793f431b6f54fd18a76 -/
section Source2840
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialEnergyCallerSelector
namespace SevenEighths.InverseInitialEnergyCallerPool
local notation "Eis" => ActualEisensteinCubic.O

theorem residual_factors_in_pool (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hne : (columns S P j).Nonempty)
    {Q : Ideal Eis} (hQ : Q∈normalizedFactors (residual P j)) :
    Q∈primePool (columns S P j) := by
  obtain ⟨c,hc⟩ := hne
  obtain ⟨hcs,_,hPc,_⟩ := (mem_columns hP hj).mp hc
  apply mem_primePool_iff.mpr
  refine ⟨c,hc,?_⟩
  exact Multiset.mem_of_le
    ((dvd_iff_normalizedFactors_le_normalizedFactors
      (residual_squarefree hP hj).ne_zero hcs.ne_zero).mp hPc) hQ

def forcedSlots (S : Finset (Ideal Eis)) (P j : Ideal Eis) :
    Finset (primePool (columns S P j)) := idealSupport (columns S P j) (residual P j)

theorem forcedSlots_image (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hne : (columns S P j).Nonempty) :
    (forcedSlots S P j).image Subtype.val = IdealMobiusDivisorSum.primeSupport (residual P j) := by
  ext Q
  constructor
  · rintro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    exact Multiset.mem_toFinset.mpr ((mem_idealSupport_iff _ _ i).mp hi)
  · intro hQ
    have hf : Q∈normalizedFactors (residual P j) := Multiset.mem_toFinset.mp hQ
    let i : primePool (columns S P j) := ⟨Q,residual_factors_in_pool S hP hj hne hf⟩
    exact Finset.mem_image.mpr ⟨i,(mem_idealSupport_iff _ _ i).mpr hf,rfl⟩

theorem forcedSlots_product (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hne : (columns S P j).Nonempty) :
    (∏ i∈forcedSlots S P j,i.val)=residual P j := by
  calc
    _ = ∏ Q∈(forcedSlots S P j).image Subtype.val,Q := by
      rw [Finset.prod_image]
      exact fun a _ b _ h=>Subtype.val_injective h
    _ = _ := by rw [forcedSlots_image S hP hj hne]
                exact squarefree_support_product_self (residual_squarefree hP hj)

theorem original_selector_forced_slots
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hne : (columns S P j).Nonempty) (a : Ideal Eis→ℂ) (W : Ideal Eis→ℂ)
    (A : Finset (primePool (columns S P j)))
    (hA : Squarefree (∏ i∈A,i.val))
    (hcover : residual P j∣(∏ i∈A,i.val) → W (∏ i∈A,i.val)≠0 →
      IsCoprime (∏ i∈A,i.val) j → reconstruct P j (∏ i∈A,i.val)∈S) :
    reconstructedSelector S P j a A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) =
    a (reconstruct P j (∏ i∈A,i.val)) *
      SevenEighths.InverseMoment.primeMark (forcedSlots S P j) (fun i=>{i})
        (fun _ _=>(1:ℂ)) A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) :=
  reconstructedSelector_forced_mark S hP hj a W (forcedSlots S P j) A
    (forcedSlots_product S hP.2.1 hj hne) hA hcover

end SevenEighths.InverseInitialEnergyCallerPool

end

end OAI

end Source2840

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerWindow.lean; sha256: ed0c37bc7fc0291b6711f61d964591a07ccf4dc147af53bf61b9bf732ca158b2 -/
section Source2841
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialKernelBridge SevenEighths.InverseInitialEnergyCallerPool
namespace SevenEighths.InverseInitialEnergyCallerWindow
local notation "Eis" => ActualEisensteinCubic.O

def originalSource (Z r b : ℝ) : Finset (Ideal Eis) :=
  (idealsUpTo ⌈Z^r*b⌉₊).filter Supported

theorem originalSource_supported (Z r b : ℝ) :
    ∀n∈originalSource Z r b,Squarefree n→Supported n := by
  intro n hn _
  exact (Finset.mem_filter.mp hn).2

theorem residual_window_eq (W : ℝ→ℂ) {P j c : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hc : residual P j∣c)
    (Z r z G : ℝ) (hZ : 0<Z) :
    residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G)) =
      W (((reconstruct P j c).absNorm:ℝ)/Z^r) := by
  unfold residualOverlapWindow
  rw [←scaled_cutoff_argument hP hj hc hZ r z G]

theorem reconstructed_mem_originalSource
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0<Z) (hW : ∀x,W x≠0→x≤b)
    {P j c : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hc : Admissible c) (hPc : residual P j∣c)
    (hlive : residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G))≠0) :
    reconstruct P j c∈originalSource Z r b := by
  have hs : Supported (reconstruct P j c) :=
    (supported_mul_iff _ _).mpr
      ⟨admissible_supported (admissible_of_dvd hP hj),
        admissible_supported (admissible_of_dvd hc (idealQuotient_dvd hPc))⟩
  apply Finset.mem_filter.mpr
  refine ⟨InverseInitialRawDictionary.finite_source_cover W (Z^r) b
    (Real.rpow_pos_of_pos hZ r) hW _ hs.1 ?_,hs⟩
  rwa [residual_window_eq W hP.2.1 hj hPc Z r z G hZ] at hlive

theorem original_selector_window
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0<Z) (hW : ∀x,W x≠0→x≤b)
    {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hne : (columns (originalSource Z r b) P j).Nonempty)
    (a : Ideal Eis→ℂ) (A : Finset (primePool (columns (originalSource Z r b) P j))) :
    reconstructedSelector (originalSource Z r b) P j a A *
      rowCoprimeMask (fun i : primePool (columns (originalSource Z r b) P j)=>i.val)
        A (primaryGenerator j) *
      residualOverlapWindow P j W Z z G (((∏ i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) =
    a (reconstruct P j (∏ i∈A,i.val)) *
      InverseMoment.primeMark (forcedSlots (originalSource Z r b) P j) (fun i=>{i})
        (fun _ _=>(1:ℂ)) A *
      rowCoprimeMask (fun i : primePool (columns (originalSource Z r b) P j)=>i.val)
        A (primaryGenerator j) *
      residualOverlapWindow P j W Z z G (((∏ i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) := by
  have hF : ∀I∈columns (originalSource Z r b) P j,Admissible I :=
    fun I hI=>columns_admissible _ hP hj (originalSource_supported Z r b) hI
  have hA := InitialMeanSquare.poolProduct_admissible _ hF A
  apply original_selector_forced_slots _ hP hj hne a
    (fun c=>residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G))) A hA.2.1
  intro hPc hlive _
  exact reconstructed_mem_originalSource W Z r z G b hZ hW hP hj hA hPc hlive

end SevenEighths.InverseInitialEnergyCallerWindow

end

end OAI

end Source2841

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCommonPool.lean; sha256: d1edcc7cb9a714550eb981c31409cf92347c346f2e213e3a9d6b7cee33f045b7 -/
section Source2842
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonPool
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment
local notation "Eis"=>ActualEisensteinCubic.O

def commonColumns (S Ps : Finset (Ideal Eis)) (j : Ideal Eis) : Finset (Ideal Eis) :=
  Ps.biUnion (fun P=>columns S P j)

theorem columns_subset (S Ps : Finset (Ideal Eis)) (j : Ideal Eis)
    {P : Ideal Eis} (hP : P∈Ps) : columns S P j⊆commonColumns S Ps j := by
  intro c hc
  exact Finset.mem_biUnion.mpr ⟨P,hP,hc⟩

theorem common_admissible (S Ps : Finset (Ideal Eis)) (j : Ideal Eis)
    (hPs : ∀P∈Ps,Admissible P) (hj : ∀P∈Ps,j∣P)
    (hS : ∀n∈S,Squarefree n→Supported n) :
    ∀c∈commonColumns S Ps j,Admissible c := by
  intro c hc
  obtain ⟨P,hP,hc⟩ := Finset.mem_biUnion.mp hc
  exact columns_admissible S (hPs P hP) (hj P hP) hS hc

theorem common_coprime (S Ps : Finset (Ideal Eis)) (j : Ideal Eis)
    (hPs : ∀P∈Ps,Admissible P) (hj : ∀P∈Ps,j∣P) :
    ∀c∈commonColumns S Ps j,IsCoprime c j := by
  intro c hc
  obtain ⟨P,hP,hc⟩ := Finset.mem_biUnion.mp hc
  exact ((mem_columns (hPs P hP).2.1 (hj P hP)).mp hc).2.1

theorem residual_eq_common_input
    (S F : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j∣P) (hF : ∀I∈F,Admissible I)
    (hcop : ∀I∈F,IsCoprime I j) (hsub : columns S P j⊆F)
    (η : Ideal Eis→*ℂ) (a : Ideal Eis→ℂ) (W : ℝ→ℂ)
    (Z r z G : ℝ) (u : Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if (∏i∈A,i.val)∈columns S P j then
          a (reconstruct P j (∏i∈A,i.val))*residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let H : Ideal Eis→ℂ := fun c=>if c∈columns S P j then
    a (reconstruct P j c)*residualOverlapWindow P j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G)) else 0
  have hfilter : F.filter (fun c=>c∈columns S P j)=columns S P j := by
    ext c
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h=>hsub h)
  have he : (∑c∈columns S P j,
      overlapResidualCoefficient P j η a W Z r z G c*star (CanonicalRowCompletion.idealRowHom u c))=
      ∑c∈F,(moebius c:ℂ)*η c*H c*star (CanonicalRowCompletion.idealRowHom u c) := by
    conv_rhs => arg 2;ext c;dsimp only [H];simp only [mul_ite,mul_zero,ite_mul,zero_mul]
    rw [←Finset.sum_filter,hfilter]
    apply Finset.sum_congr rfl
    intro c hc
    rw [overlapCoefficient_residual]
    unfold bareOverlapCoefficient
    ring
  unfold residualNormalizedPolynomial
  rw [he,selected_conjugate_row F hF j (admissible_of_dvd hP hj) hcop η H u]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  congr 1
  funext A
  dsimp [H]
  by_cases hc : (∏i∈A,i.val)∈columns S P j
  · simp only [hc,hsub hc,ite_true]
  · simp only [hc,ite_false,ite_self]

end SevenEighths.InverseInitialCommonPool

end

end OAI

end Source2842

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCommonForcing.lean; sha256: 3e21dcfc7cd49ab09905f7408fcda6a8ecfe0fffdcc1f6da82d74dec6909a007 -/
section Source2843
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonForcing
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool
open InverseInitialEnergyCallerWindow InverseInitialEnergyCallerSelector
local notation "Eis"=>ActualEisensteinCubic.O

theorem common_selector_window
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    {P j:Ideal Eis}(hP:Admissible P)(hj:j∣P)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)(A:Finset (primePool F)) :
    (if (∏i∈A,i.val)∈columns (originalSource Z r b) P j then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j) =
    (if residual P j∣(∏i∈A,i.val) then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j) := by
  by_cases hm : rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j)=0
  · simp only [hm,mul_zero]
  by_cases hw : residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))=0
  · simp only [hw,ite_self,zero_mul]
  have hA := InitialMeanSquare.poolProduct_admissible F hF A
  have hcop := mask_nonzero_coprime F j (admissible_of_dvd hP hj) A hm
  by_cases hd : residual P j∣(∏i∈A,i.val)
  · have hmem := (mem_columns hP.2.1 hj).mpr ⟨hA.2.1,hcop,hd,
      reconstructed_mem_originalSource W Z r z G b hZ hW hP hj hA hd hw⟩
    simp only [hd,hmem,ite_true]
  · have hn : (∏i∈A,i.val)∉columns (originalSource Z r b) P j :=
      fun h=>hd ((mem_columns hP.2.1 hj).mp h).2.2.1
    simp only [hd,hn,ite_false]

theorem residual_eq_common_forcing
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    {P j:Ideal Eis}(hP:Admissible P)(hj:j∣P)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)
    (hcop:∀I∈F,IsCoprime I j)(hsub:columns (originalSource Z r b) P j⊆F)
    (η:Ideal Eis→*ℂ)(u:Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial (originalSource Z r b) P j η (fun _=>1) W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if residual P j∣(∏i∈A,i.val) then
          residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [residual_eq_common_input _ F hP hj hF hcop hsub η (fun _=>1) W Z r z G u]
  simp only [one_mul]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he := common_selector_window W Z r z G b hZ hW hP hj F hF A
  have hm : rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator j)=rowCoprimeMask (fun i:primePool F=>i.val) A
        (primaryGenerator j) := by
    congr 1
    funext i
    exact poolPrimary_span F hF i
  dsimp only
  rw [hm]
  linear_combination
    (supportMobius (fun i:primePool F=>Ideal.span {poolPrimary F i}) A *
      elementCharacter η (∏i∈A,poolPrimary F i) *
      star (finiteSquarefreeRow (fun i:primePool F=>Ideal.span {poolPrimary F i})
        (poolPrimary_good F hF) A u))*he

end SevenEighths.InverseInitialCommonForcing

end

end OAI

end Source2843

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCommonTuples.lean; sha256: 950973775b4275c48e43104b0d6255b8ca5ee4387d9297daf4396ede7838922b -/
section Source2844
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing
local notation "Eis"=>ActualEisensteinCubic.O
variable {κ ι : Type*} [DecidableEq ι]

theorem input_finset_sum (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,goodLambda∉Ideal.span {p i})(F:Finset ι)(Ψ:Eis→*ℂ)(j u:Eis)
    (T:Finset κ)(a:κ→ℂ)(H:κ→Finset ι→ℂ) :
    inputConjugateRow p hg F Ψ j 1 1 (fun A=>∑k∈T,a k*H k A) u=
      ∑k∈T,a k*inputConjugateRow p hg F Ψ j 1 1 (H k) u := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro A hA
  ring

def tupleColumns (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→Ideal Eis)(j:Ideal Eis) :
    Finset (Ideal Eis) := T.biUnion (fun k=>columns S (P k) j)

theorem tupleColumns_admissible (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→Ideal Eis)
    (j:Ideal Eis)(hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hS:∀n∈S,Squarefree n→Supported n) :
    ∀c∈tupleColumns S T P j,Admissible c := by
  intro c hc
  obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
  exact columns_admissible S (hP k hk) (hj k hk) hS hc

theorem tupleColumns_coprime (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→Ideal Eis)
    (j:Ideal Eis)(hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k) :
    ∀c∈tupleColumns S T P j,IsCoprime c j := by
  intro c hc
  obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
  exact ((mem_columns (hP k hk).2.1 (hj k hk)).mp hc).2.1

theorem original_tuples_common_input
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (T:Finset κ)(P:κ→Ideal Eis)(j:Ideal Eis)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (η:Ideal Eis→*ℂ)(a:κ→ℂ)(u:Eis) :
    let S := originalSource Z r b
    let F := tupleColumns S T P j
    let hF := tupleColumns_admissible S T P j hP hj (originalSource_supported Z r b)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑k∈T,a k*residualNormalizedPolynomial S (P k) j η (fun _=>1) W Z r z G u)=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>∑k∈T,a k*(if residual (P k) j∣(∏i∈A,i.val) then
          residualOverlapWindow (P k) j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u := by
  intro S F hF
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  erw [input_finset_sum (p := poolPrimary F)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [residual_eq_common_forcing W Z r z G b hZ hW (hP k hk) (hj k hk) F hF
    (tupleColumns_coprime S T P j hP hj)
    (fun c hc=>Finset.mem_biUnion.mpr ⟨k,hk,hc⟩) η u]
  ring

end SevenEighths.InverseInitialCommonTuples

end

end OAI

end Source2844

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCommonLists.lean; sha256: d975c83f2abc645e180c762d56fe4d7e0459668ff15fd7cba39c4038db8785ab -/
section Source2845
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
namespace SevenEighths.InverseInitialCommonLists
open InverseMoment
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def poolList (F:Finset (Ideal Eis))(L:Finset (Ideal Eis)) : Finset (primePool F) :=
  Finset.univ.filter (fun i=>i.val∈L)

theorem outside_pool_not_dvd (F:Finset (Ideal Eis))(A:Finset (primePool F))
    {P:Ideal Eis}(hP:Prime P)(hn:P∉primePool F) : ¬P∣∏i∈A,i.val := by
  intro hd
  obtain ⟨i,hi,hd⟩ := hP.dvd_finsetProd_iff (fun i:primePool F=>i.val) |>.mp hd
  have hip : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have he := (prime_dvd_prime_iff_eq hP hip).mp hd
  exact hn (he ▸ i.property)

theorem dividing_list_image (F:Finset (Ideal Eis))(L:Finset (Ideal Eis))
    (hL:∀P∈L,Prime P)(A:Finset (primePool F)) :
    ((poolList F L).filter (fun i=>i∈A)).image Subtype.val=
      L.filter (fun P=>P∣∏i∈A,i.val) := by
  ext P
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hiL,hiA⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiL).2,Finset.dvd_prod_of_mem _ hiA⟩
  · intro h
    obtain ⟨hPL,hd⟩ := Finset.mem_filter.mp h
    obtain ⟨i,hi,hd⟩ := (hL P hPL).dvd_finsetProd_iff (fun i:primePool F=>i.val) |>.mp hd
    have hip : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    have he := (prime_dvd_prime_iff_eq (hL P hPL) hip).mp hd
    refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨?_,hi⟩,he.symm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hPL⟩

theorem original_ideal_slot (F:Finset (Ideal Eis))(L:Finset (Ideal Eis))
    (hL:∀P∈L,Prime P)(a:Ideal Eis→ℂ)(A:Finset (primePool F)) :
    (∑P∈L,if P∣∏i∈A,i.val then a P else 0)=
      primeSlot (poolList F L) (fun i=>a i.val) A := by
  rw [←Finset.sum_filter,←dividing_list_image F L hL A,
    Finset.sum_image (fun i _ j _ h=>Subtype.val_injective h)]
  simp only [primeSlot,←Finset.sum_filter]

theorem original_ideal_mark (F:Finset (Ideal Eis))(I:Finset σ)
    (L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(A:Finset (primePool F)) :
    indexedIdealMark id I L a (∏i∈A,i.val)=
      primeMark I (fun i=>poolList F (L i)) (fun i q=>a i q.val) A := by
  unfold indexedIdealMark primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact original_ideal_slot F (L i) (hL i hi) (a i) A

end SevenEighths.InverseInitialCommonLists

end

end OAI

end Source2845

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCommonRatios.lean; sha256: 0e4700f64d1a624962d46f1d1d75aea7e1b459357894d892baee522b1458e67a -/
section Source2846
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve
namespace SevenEighths.InverseInitialCommonRatios
open InverseInitialOverlap InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def survivingProduct (I:Finset σ)(q:∀i∈I,Ideal Eis) : Ideal Eis :=
  ∏i∈I.attach,q i.val i.property

omit [DecidableEq σ] in
theorem actual_residual_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0) : residual (j*survivingProduct I q) j=survivingProduct I q :=
  quotient_mul_cancel hj

omit [DecidableEq σ] in
theorem residual_ratio_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(Z z G:ℝ)(hZ:0<Z)
    (hell:∑i∈I,ell i=z-G) :
    ((residual (j*survivingProduct I q) j).absNorm:ℝ)/Z^(z-G)=
      ∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val) := by
  rw [actual_residual_product I q j hj,Finset.prod_div_distrib]
  have hp : (∏i∈I.attach,Z^(ell i.val))=Z^(z-G) := by
    rw [←Real.rpow_sum_of_pos hZ]
    rw [Finset.sum_attach,hell]
  rw [hp]
  congr 1
  simp only [survivingProduct,map_prod,Nat.cast_prod]

omit [DecidableEq σ] in
theorem original_residual_window (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)
    (hell:∑i∈I,ell i=z-G)(c:Ideal Eis) :
    residualOverlapWindow (j*survivingProduct I q) j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G))=
      W (((j.absNorm:ℝ)/Z^G)*((c.absNorm:ℝ)/Z^(r+z-2*G))/
        (∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val))) := by
  unfold residualOverlapWindow
  rw [residual_ratio_product I q j hj ell Z z G hZ hell]

end SevenEighths.InverseInitialCommonRatios

end

end OAI

end Source2846

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialOverlapIdealFourier.lean; sha256: 77f2e7a493c20aa877388dc5dce1121dccdb2b799b2c29803aeb91cec002dcfe -/
section Source2847
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic
namespace SevenEighths.InverseInitialOverlapIdealFourier
open InverseMoment InverseInitialOverlapFourier
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def activeIndices (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (c : Ideal Eis) : Finset ι := (I.biUnion L).filter (fun p=>primes p∣c)

omit [DecidableEq σ] in
theorem activeIndices_mem (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (c : Ideal Eis) {i : σ} (hi : i∈I) {p : ι} (hp : p∈L i) :
    p∈activeIndices primes I L c ↔ primes p∣c := by
  simp only [activeIndices,Finset.mem_filter]
  exact and_iff_right (Finset.mem_biUnion.mpr ⟨i,hi,hp⟩)

theorem indexed_mark_active (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (c : Ideal Eis) :
    indexedIdealMark primes I L a c=primeMark I L a (activeIndices primes I L c) := by
  unfold indexedIdealMark primeMark primeSlot
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro p hp
  simp only [activeIndices_mem primes I L c hi hp]

theorem indexed_overlap_separation (g : 𝓢(ℝ,ℂ))
    (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (c : Ideal Eis) (xj xc : ℝ) :
    (∑p∈I.pi L,(∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)*
      g (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*logPhase t xc*
        indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c := by
  simp_rw [indexed_mark_active]
  rw [←overlap_tuple_separation]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [activeIndices_mem primes I L c i.property ((Finset.mem_pi.mp hp) i.val i.property)]

theorem indexed_overlap_integrable (g : 𝓢(ℝ,ℂ))
    (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (c : Ideal Eis) (xj xc : ℝ) :
    Integrable (fun t:ℝ=>density g xj t*logPhase t xc*
      indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c) := by
  simp_rw [indexed_mark_active]
  exact overlap_mode_integrable g I L a y _ xj xc

omit [DecidableEq σ] [DecidableEq ι] in
theorem tuple_gate_product (primes : ι→Ideal Eis) (I : Finset σ)
    (a : σ→ι→ℂ) (p : ∀i∈I,ι) (c : Ideal Eis)
    (hc : Pairwise (Function.onFun IsCoprime (fun i:I=>primes (p i.val i.property)))) :
    (∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)=
      if (∏i∈I.attach,primes (p i.val i.property))∣c then
        ∏i∈I.attach,a i.val (p i.val i.property) else 0 := by
  by_cases h : (∏i∈I.attach,primes (p i.val i.property))∣c
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i hi
    exact ite_eq_left ((Finset.dvd_prod_of_mem (fun i:I=>primes (p i.val i.property)) hi).trans h)
  · rw [ite_eq_right h]
    have hn : ∃i:I,¬primes (p i.val i.property)∣c := by
      by_contra hn
      push Not at hn
      apply h
      exact Finset.prod_dvd_of_coprime (hc.set_pairwise _) (fun i _=>hn i)
    obtain ⟨i,hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_attach _ i) (ite_eq_right hi)

theorem finite_ideal_overlap_separation (g : 𝓢(ℝ,ℂ))
    (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (C : Finset (Ideal Eis))
    (coefficient : Ideal Eis→ℂ) (xj : ℝ) (xc : Ideal Eis→ℝ) :
    (∑c∈C,coefficient c*
      ∑p∈I.pi L,(∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)*
        g (xj+xc c-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*
        ∑c∈C,coefficient c*logPhase t (xc c)*
          indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c := by
  simp_rw [indexed_overlap_separation]
  simp only [Finset.mul_sum]
  have hi (c:Ideal Eis) : Integrable (fun t:ℝ=>coefficient c*
      (density g xj t*logPhase t (xc c)*indexedIdealMark primes I L
        (fun i p=>a i p*logPhase (-t) (y i p)) c)) :=
    (indexed_overlap_integrable g primes I L a y c xj (xc c)).const_mul _
  have he (c:Ideal Eis) (t:ℝ) : density g xj t*(coefficient c*logPhase t (xc c)*
      indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c)=
      coefficient c*(density g xj t*logPhase t (xc c)*
      indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c) := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun c _=>hi c)]
  simp only [integral_const_mul]

end SevenEighths.InverseInitialOverlapIdealFourier

end

end OAI

end Source2847

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCommonProfile.lean; sha256: d9626f5f93a189486b91487db6f5a7e25902d78f76f6f6e358f75c1cbcc0c4f5 -/
section Source2848
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
namespace SevenEighths.InverseInitialCommonProfile
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios
open InverseInitialOverlapFourier InverseInitialOverlapIdealFourier
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def slotRatio (Z:ℝ)(ell:σ→ℝ)(i:σ)(P:Ideal Eis) : ℝ := (P.absNorm:ℝ)/Z^(ell i)

omit [DecidableEq σ] in
theorem slotRatio_pos (Z:ℝ)(hZ:0<Z)(ell:σ→ℝ)(i:σ){P:Ideal Eis}(hP:Prime P) :
    0<slotRatio Z ell i P := by
  apply div_pos _ (Real.rpow_pos_of_pos hZ _)
  exact_mod_cast Nat.pos_of_ne_zero (fun h=>hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))

theorem common_profile_separation
    (W:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime
      (fun i:I=>q i.val i.property)))
    (Z:ℝ)(hZ:0<Z)(ell:σ→ℝ)(A:Finset (primePool F))
    (yj yc:ℝ)(hj:0<yj)(hc:0<yc) :
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if survivingProduct I q∣(∏i∈A,i.val) then
        W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)) =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log yj) t*logPhase t (Real.log yc)*
        primeMark I (fun i=>poolList F (L i))
          (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A := by
  have hm (t:ℝ) : primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A =
      primeMark I L (fun i P=>a i P*logPhase (-t) (Real.log (slotRatio Z ell i P)))
        (activeIndices id I L (∏i∈A,i.val)) :=
    (original_ideal_mark F I L hL
      (fun i P=>a i P*logPhase (-t) (Real.log (slotRatio Z ell i P))) A).symm.trans
      (indexed_mark_active id I L _ _)
  simp_rw [hm]
  have he := actual_overlap_separation W a₀ b₀ ha₀ hs hW I L a (slotRatio Z ell)
    (fun i hi P hP=>slotRatio_pos Z hZ ell i (hL i hi P hP))
    (activeIndices id I L (∏i∈A,i.val)) yj yc hj hc
  rw [←he]
  apply Finset.sum_congr rfl
  intro q hq
  have hprod : (∏i∈I.attach,if q i.val i.property∈activeIndices id I L (∏i∈A,i.val)
      then a i.val (q i.val i.property) else 0)=
      if survivingProduct I q∣(∏i∈A,i.val) then
        ∏i∈I.attach,a i.val (q i.val i.property) else 0 := by
    calc
      _ = ∏i∈I.attach,if q i.val i.property∣(∏i∈A,i.val) then a i.val (q i.val i.property) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [activeIndices_mem id I L _ i.property ((Finset.mem_pi.mp hq) i.val i.property),id_eq]
      _ = _ := by
        convert! tuple_gate_product id I a q (∏i∈A,i.val) (hcop q hq) using 1
  rw [hprod]
  split_ifs <;> simp

theorem common_profile_integrable (g:𝓢(ℝ,ℂ))
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (a:σ→Ideal Eis→ℂ)(Z:ℝ)(ell:σ→ℝ)(A:Finset (primePool F))(yj yc:ℝ) :
    Integrable (fun t:ℝ=>density g (Real.log yj) t*logPhase t (Real.log yc)*
      primeMark I (fun i=>poolList F (L i))
        (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A) :=
  overlap_mode_integrable g I (fun i=>poolList F (L i)) (fun i q=>a i q.val)
    (fun i q=>Real.log (slotRatio Z ell i q.val)) A (Real.log yj) (Real.log yc)

end SevenEighths.InverseInitialCommonProfile

end

end OAI

end Source2848

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialOverlapInputFourier.lean; sha256: 68751f7d738215cf4c0387bc5ce65ffb0f77cf4d5ac5144b09c8960c6c62b3e5 -/
section Source2849
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic
open FirstPassCubeLabels
namespace SevenEighths.InverseInitialOverlapInputFourier
open InverseMoment InverseInitialOverlapFourier InverseInitialArithmetic InverseInitialRayAttachment
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem input_integral (F : Finset ι) (Ψ : Eis→*ℂ) (j u : Eis)
    (H : Finset ι→ℝ→ℂ) (hH : ∀A∈F.powerset,Integrable (H A)) :
    inputConjugateRow p hg F Ψ j 1 1 (fun A=>∫t:ℝ,H A t) u =
      ∫t:ℝ,inputConjugateRow p hg F Ψ j 1 1 (fun A=>H A t) u := by
  rw [initial_input_row p hg]
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  have he (A:Finset ι) (t:ℝ) :
      supportMobius (fun i=>Ideal.span {p i}) A*
        (Ψ (∏i∈A,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) A j*H A t)*
        star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u)=
      (supportMobius (fun i=>Ideal.span {p i}) A*Ψ (∏i∈A,p i)*
        rowCoprimeMask (fun i=>Ideal.span {p i}) A j*
        star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u))*H A t := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun A hA=>(hH A hA).const_mul _)]
  simp only [integral_const_mul]
  apply Finset.sum_congr rfl
  intro A hA
  ring

theorem original_overlap_input
    (hp : ∀i,p i≠0) (F : Finset ι) (Ψ : Eis→*ℂ) (j u : Eis)
    (W : ℝ→ℂ) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (hy : ∀i∈slots,∀q∈lists i,0<y i q)
    (wFresh : ℝ→ℂ) (Z D yj : ℝ) (hZ : 0<Z) (hj : 0<yj) :
    ((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
      (fun A=>wFresh (primeProductNorm p A/Z^D)*
        ∑q∈slots.pi lists,
          (∏i∈slots.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*(primeProductNorm p A/Z^D)/(∏i∈slots.attach,y i.val (q i.val i.property)))) u =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
          (initialTest p
            (primeMark slots lists (fun i q=>a i q*logPhase (-t) (Real.log (y i q))))
            (childLogTest wFresh t) Z D) u) := by
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset ι→ℝ→ℂ := fun A t=>density g (Real.log yj) t*
    (primeMark slots lists (fun i q=>a i q*logPhase (-t) (Real.log (y i q))) A*
      childLogTest wFresh t (primeProductNorm p A/Z^D))
  have hH (A:Finset ι) : Integrable (H A) := by
    have hi := (overlap_mode_integrable g slots lists a (fun i q=>Real.log (y i q))
      A (Real.log yj) (Real.log (primeProductNorm p A/Z^D))).const_mul
      (wFresh (primeProductNorm p A/Z^D))
    convert hi using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have he (A:Finset ι) :
      wFresh (primeProductNorm p A/Z^D)*
        (∑q∈slots.pi lists,
          (∏i∈slots.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*(primeProductNorm p A/Z^D)/(∏i∈slots.attach,y i.val (q i.val i.property)))) =
      ∫t:ℝ,H A t := by
    rw [actual_overlap_separation W a₀ b₀ ha₀ hs hW slots lists a y hy A yj
      (primeProductNorm p A/Z^D) hj
      (div_pos (primeProductNorm_pos p hp A) (Real.rpow_pos_of_pos hZ D)),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [H,childLogTest,g]
    ring
  simp_rw [he]
  rw [input_integral p hg F Ψ j u H (fun A _=>hH A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialOverlapInputFourier

end

end OAI

end Source2849

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialOverlapFresh.lean; sha256: 77a56ccb0260fc2496052ff47e1a72c743b440a1b5f5abdc1c17df31cede88cc -/
section Source2850
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialOverlapFresh
variable {σ : Type*} [DecidableEq σ]

omit [DecidableEq σ] in
theorem overlap_column_interval (I : Finset σ) (lo hi y : σ→ℝ)
    (a b jlo jhi yj yc : ℝ) (ha : 0<a) (hab : a≤b)
    (hlo : ∀i∈I,0<lo i) (hy : ∀i∈I,y i∈Set.Icc (lo i) (hi i))
    (hjlo : 0<jlo) (hj : yj∈Set.Icc jlo jhi) (hc : 0<yc)
    (hsource : yj*yc/(∏i∈I,y i)∈Set.Icc a b) :
    yc∈Set.Icc (a*(∏i∈I,lo i)/jhi) (b*(∏i∈I,hi i)/jlo) := by
  have hyp : ∀i∈I,0<y i := fun i hi=>(hlo i hi).trans_le (hy i hi).1
  have hip : ∀i∈I,0<hi i := fun i hi=>(hyp i hi).trans_le (hy i hi).2
  have hprod : 0<∏i∈I,y i := Finset.prod_pos hyp
  have hloP : (∏i∈I,lo i)≤∏i∈I,y i :=
    Finset.prod_le_prod₀ (fun i hi=>(hlo i hi).le) (fun i hi=>(hy i hi).1)
  have hhiP : (∏i∈I,y i)≤∏i∈I,hi i :=
    Finset.prod_le_prod₀ (fun i hi=>(hyp i hi).le) (fun i hi=>(hy i hi).2)
  have hyj : 0<yj := hjlo.trans_le hj.1
  have hjhip : 0<jhi := hyj.trans_le hj.2
  have hsourceLo := (le_div_iff₀ hprod).mp hsource.1
  have hsourceHi := (div_le_iff₀ hprod).mp hsource.2
  constructor
  · apply (div_le_iff₀ hjhip).mpr
    calc
      a*(∏i∈I,lo i)≤a*(∏i∈I,y i) := mul_le_mul_of_nonneg_left hloP ha.le
      _≤yj*yc := hsourceLo
      _≤jhi*yc := mul_le_mul_of_nonneg_right hj.2 hc.le
      _=yc*jhi := mul_comm _ _
  · apply (le_div_iff₀ hjlo).mpr
    calc
      yc*jlo=jlo*yc := mul_comm _ _
      _≤yj*yc := mul_le_mul_of_nonneg_right hj.1 hc.le
      _≤b*(∏i∈I,y i) := hsourceHi
      _≤b*(∏i∈I,hi i) := mul_le_mul_of_nonneg_left hhiP (ha.le.trans hab)

omit [DecidableEq σ] in
theorem exists_overlap_fresh (I : Finset σ) (lo hi : σ→ℝ)
    (a b jlo jhi : ℝ) (ha : 0<a) (hab : a≤b)
    (hlo : ∀i∈I,0<lo i) (hhi : ∀i∈I,lo i≤hi i)
    (hjlo : 0<jlo) (hjhi : jlo≤jhi) :
    ∃(wFresh : 𝓢(ℝ,ℂ))(A B:ℝ),0<A ∧ A≤B ∧
      HasCompactSupport (wFresh:ℝ→ℂ) ∧ tsupport (wFresh:ℝ→ℂ)⊆Set.Icc A B ∧
      ∀(W:ℝ→ℂ),(Function.support W⊆Set.Icc a b)→
      ∀(y:σ→ℝ)(yj yc:ℝ),
      (∀i∈I,y i∈Set.Icc (lo i) (hi i))→yj∈Set.Icc jlo jhi→0<yc→
      W (yj*yc/(∏i∈I,y i))≠0→wFresh yc=1 := by
  let lower := a*(∏i∈I,lo i)/jhi
  let upper := b*(∏i∈I,hi i)/jlo
  have hl : 0<lower := div_pos (mul_pos ha (Finset.prod_pos hlo)) (hjlo.trans_le hjhi)
  have hu : 0<upper := div_pos (mul_pos (ha.trans_le hab)
    (Finset.prod_pos (fun i hi=>(hlo i hi).trans_le (hhi i hi)))) hjlo
  obtain ⟨w,hwc,hwone,hws⟩ := InverseSecondChildWindows.positive_cutoff
    lower (lower+upper+1) hl (by linarith)
  refine ⟨w,lower/2,lower+upper+2,half_pos hl,by linarith,hwc,?_,?_⟩
  · convert hws using 1 ; ring_nf
  · intro W hW y yj yc hy hj hc hn
    have hb := overlap_column_interval I lo hi y a b jlo jhi yj yc ha hab hlo hy hjlo hj hc (hW hn)
    apply hwone
    exact ⟨hb.1,by change yc≤lower+upper+1;have := hb.2;change yc≤upper at this;linarith⟩

end SevenEighths.InverseInitialOverlapFresh

end

end OAI

end Source2850

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialOverlapSource.lean; sha256: 99d26b2835a74516396126cc0ec2323dddb3777ce3157f0d1fcc4c4377e6456d -/
section Source2851
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialOverlapSource
open InverseInitialOverlapFresh InverseInitialOverlapInputFourier
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def tupleCoordinate (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) (i : σ) : ℝ :=
  if hi:i∈I then y i (q i hi) else 1

omit [DecidableEq ι] in
theorem tupleCoordinate_product (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) :
    (∏i∈I,tupleCoordinate I y q i)=∏i∈I.attach,y i.val (q i.val i.property) := by
  rw [←Finset.prod_attach]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [tupleCoordinate,dite_eq_left i.property]

theorem insert_original_fresh
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (lo hi : σ→ℝ) (W wFresh : ℝ→ℂ) (a₀ b₀ jlo jhi : ℝ)
    (_hW : Function.support W⊆Set.Icc a₀ b₀)
    (ha : ∀i∈I,∀q∈L i,a i q≠0→y i q∈Set.Icc (lo i) (hi i))
    (hFresh : ∀(v:σ→ℝ)(yj yc:ℝ),
      (∀i∈I,v i∈Set.Icc (lo i) (hi i))→yj∈Set.Icc jlo jhi→0<yc→
      W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (A : Finset ι) (yj yc : ℝ) (hj : yj∈Set.Icc jlo jhi) (hc : 0<yc) :
    wFresh yc*(∑q∈I.pi L,
      (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
        W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))) =
      ∑q∈I.pi L,
        (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hz : (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)=0
  · simp only [hz,zero_mul,mul_zero]
  by_cases hw : W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))=0
  · simp only [hw,mul_zero]
  have hcoord : ∀i∈I,tupleCoordinate I y q i∈Set.Icc (lo i) (hi i) := by
    intro i hi
    have hn := Finset.prod_ne_zero_iff.mp hz ⟨i,hi⟩ (Finset.mem_attach _ _)
    have hcoeff : a i (q i hi)≠0 := by
      intro he
      apply hn
      split_ifs
      · exact he
      · rfl
    simpa only [tupleCoordinate,dite_eq_left hi] using
      ha i hi (q i hi) ((Finset.mem_pi.mp hq) i hi) hcoeff
  have hf := hFresh (tupleCoordinate I y q) yj yc hcoord hj hc
    (by rwa [tupleCoordinate_product])
  rw [hf,one_mul]

theorem exists_original_overlap_input
    (I : Finset σ) (lo hi : σ→ℝ) (W : ℝ→ℂ)
    (a₀ b₀ jlo jhi : ℝ) (ha₀ : 0<a₀) (hab : a₀≤b₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (hlo : ∀i∈I,0<lo i) (hhi : ∀i∈I,lo i≤hi i)
    (hjlo : 0<jlo) (hjhi : jlo≤jhi) :
    ∃(wFresh : 𝓢(ℝ,ℂ))(A B:ℝ),0<A ∧ A≤B ∧
      HasCompactSupport (wFresh:ℝ→ℂ) ∧ tsupport (wFresh:ℝ→ℂ)⊆Set.Icc A B ∧
      ∀(p:ι→ActualEisensteinCubic.O)(_hp:∀i,p i≠0)
        (hpmax:∀i,(Ideal.span {p i}).IsMaximal)
        (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
        (F:Finset ι)(Ψ:ActualEisensteinCubic.O→*ℂ)(j u:ActualEisensteinCubic.O)
        (lists:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
        (_hy:∀i∈I,∀q∈lists i,0<y i q)
        (_ha:∀i∈I,∀q∈lists i,a i q≠0→y i q∈Set.Icc (lo i) (hi i))
        (Z D yj:ℝ)(_hZ:0<Z)(_hj:yj∈Set.Icc jlo jhi),
      letI := hpmax
      ((Z^(-D/2):ℝ):ℂ)*SecondPassArithmetic.inputConjugateRow p hg F Ψ j 1 1
        (fun U=>∑q∈I.pi lists,
          (∏i∈I.attach,if q i.val i.property∈U then a i.val (q i.val i.property) else 0)*
            W (yj*(FirstPassCubeLabels.primeProductNorm p U/Z^D)/
              (∏i∈I.attach,y i.val (q i.val i.property)))) u =
        ∫t:ℝ,InverseInitialOverlapFourier.density
          (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
          (((Z^(-D/2):ℝ):ℂ)*SecondPassArithmetic.inputConjugateRow p hg F Ψ j 1 1
            (InverseInitialRayAttachment.initialTest p
              (InverseMoment.primeMark I lists
                (fun i q=>a i q*FourierBridge.logPhase (-t) (Real.log (y i q))))
              (InverseMoment.childLogTest wFresh t) Z D) u) := by
  obtain ⟨w,A,B,hA,hAB,hwc,hws,hfresh⟩ := exists_overlap_fresh I lo hi a₀ b₀ jlo jhi
    ha₀ hab hlo hhi hjlo hjhi
  refine ⟨w,A,B,hA,hAB,hwc,hws,?_⟩
  intro p hp hpmax hg F Ψ j u lists a y hy ha Z D yj hZ hj
  let := hpmax
  have he := original_overlap_input p hg hp F Ψ j u W a₀ b₀ ha₀ hs hW
    I lists a y hy w Z D yj hZ (hjlo.trans_le hj.1)
  convert he using 2
  apply congrArg (fun H:Finset ι→ℂ=>SecondPassArithmetic.inputConjugateRow p hg F Ψ j 1 1 H u)
  funext U
  exact (insert_original_fresh I lists a y lo hi W w a₀ b₀ jlo jhi hs ha
    (hfresh W hs) U yj (FirstPassCubeLabels.primeProductNorm p U/Z^D) hj
    (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U)
      (Real.rpow_pos_of_pos hZ D))).symm

end SevenEighths.InverseInitialOverlapSource

end

end OAI

end Source2851

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCommonCutoff.lean; sha256: d25a54ac14a4e7eb0004a2d8a6a573fb31faa8b5d9a07a1380d7252d6600e803 -/
section Source2852
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
namespace SevenEighths.InverseInitialCommonCutoff
open InverseMoment InverseInitialCommonProfile InverseInitialCommonRatios
open InverseInitialOverlapIdealFourier InverseInitialOverlapSource
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

def tupleProfile (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (Z:ℝ)(ell:σ→ℝ)(W:ℝ→ℂ)(yj yc:ℝ)(c:Ideal Eis) : ℂ :=
  ∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
    (if survivingProduct I q∣c then
      W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)

theorem tupleProfile_gates (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(ell:σ→ℝ)(W:ℝ→ℂ)(yj yc:ℝ)(c:Ideal Eis) :
    tupleProfile I L a Z ell W yj yc c=
      ∑q∈I.pi L,
        (∏i∈I.attach,if q i.val i.property∈activeIndices id I L c then a i.val (q i.val i.property) else 0)*
          W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) := by
  apply Finset.sum_congr rfl
  intro q hq
  have hg : (∏i∈I.attach,if q i.val i.property∈activeIndices id I L c then a i.val (q i.val i.property) else 0)=
      if survivingProduct I q∣c then ∏i∈I.attach,a i.val (q i.val i.property) else 0 := by
    calc
      _ = ∏i∈I.attach,if q i.val i.property∣c then a i.val (q i.val i.property) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [activeIndices_mem id I L _ i.property ((Finset.mem_pi.mp hq) i.val i.property),id_eq]
      _ = _ := by
        convert! tuple_gate_product id I a q c (hcop q hq) using 1
  rw [hg]
  split_ifs <;> simp

theorem tupleProfile_insert_fresh
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(ell lo hi:σ→ℝ)(W wFresh:ℝ→ℂ)(a₀ b₀ jlo jhi:ℝ)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hc:0<yc)(c:Ideal Eis) :
    wFresh yc*tupleProfile I L a Z ell W yj yc c=tupleProfile I L a Z ell W yj yc c := by
  rw [tupleProfile_gates I L a hcop]
  exact insert_original_fresh I L a (slotRatio Z ell) lo hi W wFresh a₀ b₀ jlo jhi
    hs ha hFresh (activeIndices id I L c) yj yc hj hc

end SevenEighths.InverseInitialCommonCutoff

end

end OAI

end Source2852

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCommonTransform.lean; sha256: 4dbfe0cb1619f492a4cdba7620831a0e55f09a7fb7d429e0dac07b5965451f94 -/
section Source2853
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic FirstPassCubeLabels
namespace SevenEighths.InverseInitialCommonTransform
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

theorem original_profile_point
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)(jlo jhi:ℝ)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (A:Finset (primePool F))(yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hjpos:0<yj)(hc:0<yc) :
    tupleProfile I L a Z ell W yj yc (∏i∈A,i.val)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        (primeMark I (fun i=>poolList F (L i))
          (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
          childLogTest wFresh t yc) := by
  have he := common_profile_separation W a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell A yj yc hjpos hc
  have hcut := tupleProfile_insert_fresh I L a hcop Z ell lo hi W wFresh a₀ b₀ jlo jhi hs ha hFresh yj yc hj hc (∏i∈A,i.val)
  rw [←hcut]
  unfold tupleProfile
  rw [he,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  unfold childLogTest
  ring

theorem original_tuples_fourier
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(j:Ideal Eis)(hj0:j≠0)
    (hP:∀q∈I.pi L,Admissible (j*survivingProduct I q))
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (η:Ideal Eis→*ℂ)(u:Eis)(Z r z G:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)
    (hell:∑i∈I,ell i=z-G)(jlo jhi:ℝ)
    (hj:((j.absNorm:ℝ)/Z^G)∈Set.Icc jlo jhi)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1) :
    let S := originalSource Z r b₀
    let P := fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q
    let F := tupleColumns S (I.pi L) P j
    let hF := tupleColumns_admissible S (I.pi L) P j hP
      (fun q _=>dvd_mul_right j _) (originalSource_supported Z r b₀)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      residualNormalizedPolynomial S (P q) j η (fun _=>1) W Z r z G u)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log ((j.absNorm:ℝ)/Z^G)) t*
        (((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
          (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (initialTest (poolPrimary F)
            (primeMark I (fun i=>poolList F (L i))
              (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))))
            (childLogTest wFresh t) Z (r+z-2*G)) u) := by
  intro S P F hF
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hjpos : 0<(j.absNorm:ℝ)/Z^G := by
    apply div_pos _ (Real.rpow_pos_of_pos hZ G)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset (primePool F)→ℝ→ℂ := fun A t=>density g (Real.log ((j.absNorm:ℝ)/Z^G)) t*
    (primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
      childLogTest wFresh t (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
  have hHi (A:Finset (primePool F)) : Integrable (H A) := by
    have hh := (common_profile_integrable g F I L a Z ell A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))).const_mul
      (wFresh (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
    convert hh using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have hpoint (A:Finset (primePool F)) :
      (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
        (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))=∫t:ℝ,H A t := by
    dsimp only [P]
    simp_rw [actual_residual_product I _ j hj0,original_residual_window I _ j hj0 ell W Z r z G hZ hell]
    apply original_profile_point W wFresh a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell lo hi jlo jhi ha hFresh A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) hj hjpos
    apply div_pos _ (Real.rpow_pos_of_pos hZ _)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>(InitialMeanSquare.poolProduct_admissible F hF A).1
      (Ideal.absNorm_eq_zero_iff.mp h))
  rw [original_tuples_common_input W Z r z G b₀ hZ (fun x hx=>(hs hx).2)
    (I.pi L) P j hP (fun q _=>dvd_mul_right j _) η (fun q=>∏i∈I.attach,a i.val (q i.val i.property)) u]
  change ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
    (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) 1 1
    (fun A=>∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u = _
  rw [show (fun A:Finset (primePool F)=>∑q∈I.pi L,
    (∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) = (fun A=>∫t:ℝ,H A t)
    from funext hpoint]
  rw [input_integral (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) u H (fun A _=>hHi A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest,InitialMeanSquare.poolPrimary_norm F hF]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialCommonTransform

end

end OAI

end Source2853

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialLargePool.lean; sha256: 6e3011923fa8d25d1ab6bde05db5653c196f883c282f978acdca2b39dec61a5f -/
section Source2854
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic UniqueFactorizationMonoid CanonicalRowCompletion
namespace SevenEighths.InverseInitialLargePool
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing InverseInitialCommonTuples
local notation "Eis"=>ActualEisensteinCubic.O
local notation "O"=>ActualEisensteinCubic.O
theorem selected_conjugate_row_supported (F : Finset (Ideal O))
    (hF : ∀ I ∈ F,Admissible I) (j : Ideal O) (hj : Admissible j)
    (η : Ideal O →* ℂ) (H : Ideal O → ℂ)
    (hcop : ∀ I ∈ F,H I≠0→IsCoprime I j) (u : O) :
    let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    (∑ I ∈ F,(moebius I : ℂ)*η I*H I*star (idealRowHom u I)) =
      inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A => if (∏ i ∈ A,i.val)∈F then H (∏ i ∈ A,i.val) else 0) u := by
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) =
      (fun i : primePool F => i.val) := funext (poolPrimary_span F hF)
  dsimp only
  rw [InitialMeanSquare.sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [elementCharacter_product]
  simp only [he]
  by_cases hAF : (∏ i ∈ A,i.val)∈F
  · simp only [hAF,ite_true]
    by_cases hh:H (∏i∈A,i.val)=0
    · simp only [hh,mul_zero,zero_mul]
    rw [selected_mask F j hj A (hcop _ hAF hh),mul_one]
    rw [idealRowHom_eq_idealSexticRow F hF hAF]
    simp only [supportMobius,idealSexticRow,InitialMeanSquare.pool_support_product]
    ring
  · simp only [hAF,ite_false,mul_zero,zero_mul]

theorem residual_eq_large_input
    (S F : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j∣P) (hF : ∀I∈F,Admissible I)
    (hsub : columns S P j⊆F)
    (η : Ideal Eis→*ℂ) (a : Ideal Eis→ℂ) (W : ℝ→ℂ)
    (Z r z G : ℝ) (u : Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if (∏i∈A,i.val)∈columns S P j then
          a (reconstruct P j (∏i∈A,i.val))*residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let H : Ideal Eis→ℂ := fun c=>if c∈columns S P j then
    a (reconstruct P j c)*residualOverlapWindow P j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G)) else 0
  have hfilter : F.filter (fun c=>c∈columns S P j)=columns S P j := by
    ext c
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h=>hsub h)
  have he : (∑c∈columns S P j,
      overlapResidualCoefficient P j η a W Z r z G c*star (CanonicalRowCompletion.idealRowHom u c))=
      ∑c∈F,(moebius c:ℂ)*η c*H c*star (CanonicalRowCompletion.idealRowHom u c) := by
    conv_rhs => arg 2;ext c;dsimp only [H];simp only [mul_ite,mul_zero,ite_mul,zero_mul]
    rw [←Finset.sum_filter,hfilter]
    apply Finset.sum_congr rfl
    intro c hc
    rw [overlapCoefficient_residual]
    unfold bareOverlapCoefficient
    ring
  unfold residualNormalizedPolynomial
  have hcH : ∀I∈F,H I≠0→IsCoprime I j := by
    intro I hIF hHI
    by_cases hi:I∈columns S P j
    · exact ((mem_columns hP.2.1 hj).mp hi).2.1
    · exact False.elim (hHI (by simp [H,hi]))
  rw [he,selected_conjugate_row_supported F hF j (admissible_of_dvd hP hj) η H hcH u]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  congr 1
  funext A
  dsimp [H]
  by_cases hc : (∏i∈A,i.val)∈columns S P j
  · simp only [hc,hsub hc,ite_true]
  · simp only [hc,ite_false,ite_self]

theorem residual_eq_large_forcing
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    {P j:Ideal Eis}(hP:Admissible P)(hj:j∣P)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)
    (hsub:columns (originalSource Z r b) P j⊆F)
    (η:Ideal Eis→*ℂ)(u:Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial (originalSource Z r b) P j η (fun _=>1) W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if residual P j∣(∏i∈A,i.val) then
          residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [residual_eq_large_input _ F hP hj hF hsub η (fun _=>1) W Z r z G u]
  simp only [one_mul]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he := common_selector_window W Z r z G b hZ hW hP hj F hF A
  have hm : rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator j)=rowCoprimeMask (fun i:primePool F=>i.val) A
        (primaryGenerator j) := by
    congr 1
    funext i
    exact poolPrimary_span F hF i
  dsimp only
  rw [hm]
  linear_combination
    (supportMobius (fun i:primePool F=>Ideal.span {poolPrimary F i}) A *
      elementCharacter η (∏i∈A,poolPrimary F i) *
      star (finiteSquarefreeRow (fun i:primePool F=>Ideal.span {poolPrimary F i})
        (poolPrimary_good F hF) A u))*he

variable {κ:Type*}
theorem original_tuples_large_input
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (T:Finset κ)(P:κ→Ideal Eis)(j:Ideal Eis)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)
    (hsub:tupleColumns (originalSource Z r b) T P j⊆F)
    (η:Ideal Eis→*ℂ)(a:κ→ℂ)(u:Eis) :
    let S := originalSource Z r b
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑k∈T,a k*residualNormalizedPolynomial S (P k) j η (fun _=>1) W Z r z G u)=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>∑k∈T,a k*(if residual (P k) j∣(∏i∈A,i.val) then
          residualOverlapWindow (P k) j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u := by
  intro S
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [input_finset_sum (poolPrimary F) (poolPrimary_good F hF)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [residual_eq_large_forcing W Z r z G b hZ hW (hP k hk) (hj k hk) F hF
    (fun c hc=>hsub (Finset.mem_biUnion.mpr ⟨k,hk,hc⟩)) η u]
  ring

end SevenEighths.InverseInitialLargePool

end

end OAI

end Source2854

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialLargeFourier.lean; sha256: 7eee425238b0df174f668893377bb22c9a635447cc3b5d1cc7f09f15f73a3814 -/
section Source2855
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic FirstPassCubeLabels
namespace SevenEighths.InverseInitialLargeFourier
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

open InverseInitialCommonTransform InverseInitialLargePool
theorem original_tuples_large_fourier
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(j:Ideal Eis)(hj0:j≠0)
    (hP:∀q∈I.pi L,Admissible (j*survivingProduct I q))
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (η:Ideal Eis→*ℂ)(u:Eis)(Z r z G:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)
    (hell:∑i∈I,ell i=z-G)(jlo jhi:ℝ)
    (hj:((j.absNorm:ℝ)/Z^G)∈Set.Icc jlo jhi)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (F:Finset (Ideal Eis))(hF:∀c∈F,Admissible c)
    (hsub:tupleColumns (originalSource Z r b₀) (I.pi L)
      (fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q) j⊆F) :
    let S := originalSource Z r b₀
    let P := fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      residualNormalizedPolynomial S (P q) j η (fun _=>1) W Z r z G u)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log ((j.absNorm:ℝ)/Z^G)) t*
        (((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
          (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (initialTest (poolPrimary F)
            (primeMark I (fun i=>poolList F (L i))
              (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))))
            (childLogTest wFresh t) Z (r+z-2*G)) u) := by
  intro S P
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hjpos : 0<(j.absNorm:ℝ)/Z^G := by
    apply div_pos _ (Real.rpow_pos_of_pos hZ G)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset (primePool F)→ℝ→ℂ := fun A t=>density g (Real.log ((j.absNorm:ℝ)/Z^G)) t*
    (primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
      childLogTest wFresh t (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
  have hHi (A:Finset (primePool F)) : Integrable (H A) := by
    have hh := (common_profile_integrable g F I L a Z ell A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))).const_mul
      (wFresh (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
    convert hh using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have hpoint (A:Finset (primePool F)) :
      (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
        (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))=∫t:ℝ,H A t := by
    dsimp only [P]
    simp_rw [actual_residual_product I _ j hj0,original_residual_window I _ j hj0 ell W Z r z G hZ hell]
    apply original_profile_point W wFresh a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell lo hi jlo jhi ha hFresh A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) hj hjpos
    apply div_pos _ (Real.rpow_pos_of_pos hZ _)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>(InitialMeanSquare.poolProduct_admissible F hF A).1
      (Ideal.absNorm_eq_zero_iff.mp h))
  rw [original_tuples_large_input W Z r z G b₀ hZ (fun x hx=>(hs hx).2)
    (I.pi L) P j hP (fun q _=>dvd_mul_right j _) F hF hsub η (fun q=>∏i∈I.attach,a i.val (q i.val i.property)) u]
  change ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
    (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) 1 1
    (fun A=>∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u = _
  rw [show (fun A:Finset (primePool F)=>∑q∈I.pi L,
    (∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) = (fun A=>∫t:ℝ,H A t)
    from funext hpoint]
  rw [input_integral (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) u H (fun A _=>hHi A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest,InitialMeanSquare.poolPrimary_norm F hF]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialLargeFourier

end

end OAI

end Source2855

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCompletePool.lean; sha256: a142f316fc490c7319eb4a0272e367e80f774b3cba70b8a257262af8122febf5 -/
section Source2856
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialCompletePool
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialLargePool
open InverseInitialCommonTuples InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O

private theorem bad_prime (P:Ideal Eis)(hP:P∈fixedBadPrimes) : Prime P := by
  rcases Finset.mem_insert.mp hP with hP|hP
  · subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
      lambdaIdeal_maximal.isPrime
  · have he := Finset.mem_singleton.mp hP
    subst P
    exact Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (2:Eis)≠0))
      twoIdeal_maximal.isPrime

theorem admissible_mem_complete {I:Ideal Eis}(hI:Admissible I)(D:ℕ)
    (hD:I.absNorm≤D) : I∈InitialMeanSquare.outsideSquarefreeIdeals fixedBadPrimes D := by
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,hD,?_⟩,hI.2.1⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hI.1 (Ideal.absNorm_eq_zero_iff.mp h))
  · intro P hP hPI
    have hp := bad_prime P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hfac := (mem_normalizedFactors_iff hI.1).mpr ⟨hp,hPI⟩
    exact (prime_good_iff_not_bad P).mp (hI.2.2 P hfac) hP

theorem original_column_norm_bound (S:Finset (Ideal Eis)){P j c:Ideal Eis}
    (hP:Admissible P)(hj:j∣P)(hc:c∈columns S P j) :
    c.absNorm≤S.sup Ideal.absNorm*P.absNorm := by
  obtain ⟨hcs,hcj,hres,hnS⟩ := (mem_columns hP.2.1 hj).mp hc
  have hn := norm_reconstruct hres
  have hj0 := (admissible_of_dvd hP hj).1
  have hjpos : 1≤j.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  have hnn : (reconstruct P j c).absNorm≤S.sup Ideal.absNorm := Finset.le_sup hnS
  have hPN : (residual P j).absNorm≤P.absNorm := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h=>hP.1 (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm (idealQuotient_dvd hj))
  calc
    c.absNorm≤j.absNorm*c.absNorm := Nat.le_mul_of_pos_left _ hjpos
    _=(reconstruct P j c).absNorm*(residual P j).absNorm := hn.symm
    _≤_ := Nat.mul_le_mul hnn hPN

theorem exists_complete_pool {κ:Type*}(S:Finset (Ideal Eis))(T:Finset κ)
    (P:κ→Ideal Eis)(j:Ideal Eis)(hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hS:∀n∈S,Squarefree n→Supported n)(bmax Xmax:ℝ)(hb:0≤bmax)(_hX:0≤Xmax) :
    ∃D:ℕ,tupleColumns S T P j⊆InitialMeanSquare.outsideSquarefreeIdeals fixedBadPrimes D ∧
      ∀b X:ℝ,0≤b→b≤bmax→0≤X→X≤Xmax→b*X≤(D:ℝ) := by
  let D := max (S.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊
  refine ⟨D,?_,?_⟩
  · intro c hc
    obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
    apply admissible_mem_complete (columns_admissible S (hP k hk) (hj k hk) hS hc)
    exact (original_column_norm_bound S (hP k hk) (hj k hk) hc).trans
      ((Nat.mul_le_mul_left (S.sup Ideal.absNorm)
        (Finset.le_sup (f:=fun k=>(P k).absNorm) hk)).trans (le_max_left _ _))
  · intro b X hb0 hbb hX0 hXX
    apply (mul_le_mul hbb hXX hX0 hb).trans
    exact (Nat.le_ceil (bmax*Xmax)).trans (by exact_mod_cast (le_max_right
      (S.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊))

end SevenEighths.InverseInitialCompletePool

end

end OAI

end Source2856

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialExcludedPool.lean; sha256: fbad197169150c4d213d48315a2ad6b33dd319f4341a03b98b1014e1b25a3a3f -/
section Source2857
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedPool
open InverseInitialOverlap InverseInitialCommonTuples InverseInitialCompletePool InverseInitialPoissonBridge
local notation "O"=>ActualEisensteinCubic.O

def outside (E:Finset (Ideal O))(I:Ideal O):Prop:=∀P∈E,¬P∣I

def originalOutside (A E:Finset (Ideal O)):Finset (Ideal O):=A.filter (outside E)

theorem column_outside (A E:Finset (Ideal O)){P j c:Ideal O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)
    (hA:∀n∈A,outside E n)(hc:c∈columns A P j):outside E c := by
  obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
  obtain ⟨hnA,hns,hg⟩:=mem_original.mp hn
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  intro Q hQ hd
  rcases (hE Q hQ).dvd_mul.mp hd with hn|hpr
  · exact hA n hnA Q hQ (hn.trans (idealQuotient_dvd hjn))
  · exact hP Q hQ (hpr.trans (idealQuotient_dvd hj))

theorem admissible_mem_excluded_complete (E:Finset (Ideal O)){I:Ideal O}
    (hI:Admissible I)(hout:outside E I)(D:ℕ)(hD:I.absNorm≤D):
    I∈InitialMeanSquare.outsideSquarefreeIdeals E D := by
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,hD,hout⟩,hI.2.1⟩
  exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)

theorem exists_excluded_complete_pool {κ:Type*}(A E:Finset (Ideal O))(T:Finset κ)
    (P:κ→Ideal O)(j:Ideal O)(hE:∀Q∈E,Prime Q)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside E (P k))
    (hA:∀n∈A,Squarefree n→Supported n)(bmax Xmax:ℝ)(hb:0≤bmax)(_hX:0≤Xmax):
    ∃D:ℕ,tupleColumns (originalOutside A E) T P j⊆
      InitialMeanSquare.outsideSquarefreeIdeals E D ∧
      ∀b X:ℝ,0≤b→b≤bmax→0≤X→X≤Xmax→b*X≤(D:ℝ) := by
  let D:=max (A.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊
  refine ⟨D,?_,?_⟩
  · intro c hc
    obtain ⟨k,hk,hc⟩:=Finset.mem_biUnion.mp hc
    have hcA:c∈columns A (P k) j:=by
      obtain ⟨n,hn,he⟩:=Finset.mem_image.mp hc
      refine Finset.mem_image.mpr ⟨n,?_,he⟩
      obtain ⟨hnA,hns,hg⟩:=mem_original.mp hn
      exact mem_original.mpr ⟨(Finset.mem_filter.mp hnA).1,hns,hg⟩
    apply admissible_mem_excluded_complete E
      (columns_admissible A (hP k hk) (hj k hk) hA hcA)
      (column_outside _ E hE (hj k hk) (hPE k hk)
        (fun n hn=>(Finset.mem_filter.mp hn).2) hc)
    exact (original_column_norm_bound A (hP k hk) (hj k hk) hcA).trans
      ((Nat.mul_le_mul_left (A.sup Ideal.absNorm)
        (Finset.le_sup (f:=fun k=>(P k).absNorm) hk)).trans (le_max_left _ _))
  · intro b X hb0 hbb hX0 hXX
    apply (mul_le_mul hbb hXX hX0 hb).trans
    exact (Nat.le_ceil (bmax*Xmax)).trans (by exact_mod_cast (le_max_right
      (A.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊))

end SevenEighths.InverseInitialExcludedPool

end

end OAI

end Source2857

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialExcludedOverlap.lean; sha256: d425248d8dba5dbce1171b79c2a954fdfc0ed6964193ae7d3263dc3375522984 -/
section Source2858
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedOverlap
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open HeckeFamily InverseInitialExcludedPolynomial
local notation "O"=>ActualEisensteinCubic.O

theorem reconstruct_outside (E:Finset (Ideal O)){P j c:Ideal O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)(hc:outside E c)
    (hres:residual P j∣c):outside E (reconstruct P j c) := by
  intro Q hQ hQn
  rcases (hE Q hQ).dvd_mul.mp hQn with hQj|hQc
  · exact hP Q hQ (hQj.trans hj)
  · exact hc Q hQ (hQc.trans (idealQuotient_dvd hres))

theorem columns_filter (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P):
    columns (originalOutside A E) P j=(columns A P j).filter (outside E) := by
  ext c
  constructor
  · intro hc
    have hd:=(mem_columns hPs hj).mp hc
    apply Finset.mem_filter.mpr
    refine ⟨(mem_columns hPs hj).mpr ⟨hd.1,hd.2.1,hd.2.2.1,?_⟩,?_⟩
    · exact (Finset.mem_filter.mp hd.2.2.2).1
    · exact column_outside _ E hE hj hP (fun n hn=>(Finset.mem_filter.mp hn).2) hc
  · intro hc
    obtain ⟨hcA,hout⟩:=Finset.mem_filter.mp hc
    obtain ⟨hcs,hcj,hres,hnA⟩:=(mem_columns hPs hj).mp hcA
    exact (mem_columns hPs hj).mpr ⟨hcs,hcj,hres,
      Finset.mem_filter.mpr ⟨hnA,reconstruct_outside E hE hj hP hout hres⟩⟩

theorem deleted_zero_outside (χ:Character)(E:Finset (Ideal O))
    (hE:∀Q∈E,Prime Q)(I:Ideal O)(hn:¬outside E I):
    idealCoeff (χ.excludePrimes E hE) I=0 := by
  rw [idealCoeff_excludePrimes]
  apply ite_eq_right
  intro hc
  apply hn
  intro Q hQ hd
  have hu:IsUnit Q:=(hc Q hQ).isRelPrime hd (dvd_refl Q)
  exact (hE Q hQ).not_isUnit hu

theorem residual_filtered (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)
    (a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(u:O):
    residualNormalizedPolynomial A P j η a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j η a W Z r z G u := by
  unfold residualNormalizedPolynomial
  rw [columns_filter A E hE hPs hj hP,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hout:outside E c
  · rw [ite_eq_left hout]
  · rw [ite_eq_right hout]
    simp only [overlapResidualCoefficient,hη c hout,mul_zero,zero_mul]

theorem residual_deleted_filtered (χ:Character)(A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P)
    (a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(u:O):
    residualNormalizedPolynomial A P j (idealCoeff (χ.excludePrimes E hE)).toMonoidHom a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j
      (idealCoeff (χ.excludePrimes E hE)).toMonoidHom a W Z r z G u :=
  residual_filtered A E hE hPs hj hP _ (deleted_zero_outside χ E hE) a W Z r z G u

end SevenEighths.InverseInitialExcludedOverlap

end

end OAI

end Source2858

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawInitialGates.lean; sha256: afd285280ae96eb3829e453d356a18ac061e2b86b640c53c8768aada0c6f9c62 -/
section Source2859
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawInitialGates
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialRayAttachment InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap InverseInitialExcludedPolynomial
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge UniqueFactorizationMonoid IdealMobiusDivisorSum
open DetectorDictionaryInverseRawGeometry
local notation "O"=>HeckeFamily.O

def basePeriod (data:RowData):ℕ:=(baseCharacter data).period

def excluded (data:RowData):Finset (Ideal O):=reflectionExcludedPrimes (basePeriod data)

def deletedBase (data:RowData):Character:=
  (baseCharacter data).excludePrimes (excluded data) (reflectionExcludedPrimes_prime (basePeriod data))

theorem basePeriod_ne_zero (data:RowData):basePeriod data≠0:=Nat.ne_of_gt (Character.period_pos _)

theorem basePeriod_le (data:RowData):Ideal.span {(basePeriod data:O)}≤(baseCharacter data).modulus:=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Character.period_mem _))

theorem raw_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (idealCoeff (deletedBase data)).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (idealCoeff (deletedBase data)).toMonoidHom):=
  deleted_physical_base_gates (baseCharacter data) (basePeriod data)
    (basePeriod_ne_zero data) (basePeriod_le data)

theorem actual_row_fixed_base (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff (data.character u) I=idealCoeff (baseCharacter data) I*idealRowHom u.val I:=by
  rw [baseCharacter_coeff]
  exact fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u) I

theorem actual_deleted_row (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) I=
      idealCoeff (deletedBase data) I*idealRowHom u.val I:=by
  unfold deletedBase excluded
  rw [idealCoeff_excludePrimes,idealCoeff_excludePrimes,actual_row_fixed_base]
  split_ifs <;> simp

def completeCutoff (H b Btree cap:ℝ):ℕ:=⌈max (Btree*H^(cap+1)) (b*H)⌉₊

theorem completeCutoff_tree (H b Btree cap:ℝ):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ):=
  (le_max_left _ _).trans (Nat.le_ceil _)

theorem completeCutoff_columns (H b Btree cap D n:ℝ)(hb:0≤b)(hD:0≤D)
    (hDH:D≤H)(hn:1≤n):b*(D/n)≤(completeCutoff H b Btree cap:ℝ):=by
  have hn0:0<n:=zero_lt_one.trans_le hn
  have hdn:D/n≤D:=(div_le_iff₀ hn0).mpr (le_mul_of_one_le_right hD hn)
  exact (mul_le_mul_of_nonneg_left (hdn.trans hDH) hb).trans
    ((le_max_right _ _).trans (Nat.le_ceil _))

theorem excluded_divisor_norm (data:RowData)(j:Ideal O)
    (hj:j∈idealDivisors (∏P∈excluded data,P)):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤((∏P∈excluded data,P).absNorm:ℝ):=by
  have hP:Squarefree (∏P∈excluded data,P):=
    prime_product_squarefree _ (reflectionExcludedPrimes_prime (basePeriod data))
  have hd: j∣∏P∈excluded data,P:=(mem_idealDivisors hP.ne_zero).mp hj
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hd
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)) (map_dvd Ideal.absNorm hd)

theorem shifted_raw_geometry_eventually (data:RowData)(c eta:ℝ)(hc:0<c)(heta:0<eta):
    ∀ᶠH:ℝ in atTop,1<H ∧ ∀D:ℝ,1≤D→D^(1+c)≤H→
      ∀j∈idealDivisors (∏P∈excluded data,P),
      let r:=Real.logb H (D/(j.absNorm:ℝ));
      -eta≤r ∧ r≤1-capacityGap c ∧ 2*r≤3-capacityGap c ∧
      H^r=D/(j.absNorm:ℝ) ∧ r+7*eta≤1+7*eta ∧ D≤H:=by
  have ht:∀ᶠH:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤H^eta:=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with H hH ht
  refine ⟨hH,?_⟩
  intro D hD hcap j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hH0:0<H:=zero_lt_one.trans hH
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  obtain ⟨hr0,hr1,hr2,hex⟩:=raw_log_capacity H D c hH hD hc hcap
  have hr:r=Real.logb H D-Real.logb H (j.absNorm:ℝ):=
    Real.logb_div hD0.ne' hn0.ne'
  have hnlog:0≤Real.logb H (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hH).le
  have hneta:Real.logb H (j.absNorm:ℝ)≤eta:=by
    exact (Real.logb_le_iff_le_rpow hH hn0).mpr (hnB.trans ht)
  have hrlo:-eta≤r:=by rw [hr];linarith
  have hrup:r≤1-capacityGap c:=by rw [hr];linarith
  refine ⟨hrlo,hrup,by rw [hr];linarith,
    Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0),?_,?_⟩
  · linarith [(capacityGap_pos c hc).le]
  · calc
      D=H^(Real.logb H D):=hex.symm
      _≤H^1:=Real.rpow_le_rpow_of_exponent_le hH.le (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _

theorem deleted_row_complete_polynomial (data:RowData)(u:NonzeroElement)
    (W:ℝ→ℂ)(H r sigma freq b:ℝ)(hH:0<H)
    (hW:∀x,W x≠0→x≤b)(Dpool:ℕ)(hbudget:b*H^r≤(Dpool:ℝ)):
    polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (H^r) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (InitialMeanSquare.outsideSquarefreeIdeals (excluded data) Dpool) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H r 0 u.val:=by
  let χ:=(data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (excluded data) Dpool
  have hs:(∑'I:Ideal O,(moebius I:ℂ)*idealCoeff χ I*
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)))=
      ∑I∈F,(moebius I:ℂ)*idealCoeff χ I*
        (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)):=by
    apply tsum_eq_sum
    intro I hn
    by_cases hsq:Squarefree I
    · by_cases hout:outside (excluded data) I
      · by_cases hw:W ((I.absNorm:ℝ)/H^r)=0
        · simp only [hw,zero_mul,mul_zero]
        · have hN:(I.absNorm:ℝ)≤(Dpool:ℝ):=
            ((div_le_iff₀ (Real.rpow_pos_of_pos hH r)).mp (hW _ hw)).trans hbudget
          have hmem:I∈F:=by
            apply Finset.mem_filter.mpr
            refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,hout⟩,hsq⟩
            · exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsq.ne_zero)
            · exact_mod_cast hN
          exact False.elim (hn hmem)
      · have hz:=deleted_zero_outside (data.character u) (excluded data)
          (reflectionExcludedPrimes_prime (basePeriod data)) I hout
        simp only [χ,hz,mul_zero,zero_mul]
    · simp only [moebius_of_not_squarefree hsq,Int.cast_zero,zero_mul]
  rw [polynomial_all_ideals,hs,normalization_eq H r hH]
  unfold InverseInitialConjugateEnergy.originalTotalPolynomial
  simp only [add_zero,map_one,mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [actual_deleted_row]
  simp only [twistedProfile,InverseInitialPoissonBridge.heckeIdealCharacter_apply]
  change (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq)) =
    (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq))
  ring

theorem raw_complete_pool (data:RowData)(H D c b Btree cap:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcap:D^(1+c)≤H)(hb:0≤b)
    (W:ℝ→ℂ)(hW:∀x,W x≠0→x≤b):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ) ∧
    ∀j∈idealDivisors (∏P∈excluded data,P),∀u:NonzeroElement,∀sigma freq:ℝ,
      polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W
        (D/(j.absNorm:ℝ)) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (InitialMeanSquare.outsideSquarefreeIdeals (excluded data)
          (completeCutoff H b Btree cap)) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H (Real.logb H (D/(j.absNorm:ℝ))) 0 u.val:=by
  refine ⟨completeCutoff_tree _ _ _ _,?_⟩
  intro j hj u sigma freq
  have hn:= (excluded_divisor_norm data j hj).1
  have hH0:0<H:=zero_lt_one.trans hH
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hex:=Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0)
  obtain ⟨_,hr,_,heD⟩:=raw_log_capacity H D c hH hD hc hcap
  have hDH:D≤H:=by
    calc
      D=H^(Real.logb H D):=heD.symm
      _≤H^1:=Real.rpow_le_rpow_of_exponent_le hH.le
        (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _
  have hbudget:b*H^(Real.logb H (D/(j.absNorm:ℝ)))≤
      (completeCutoff H b Btree cap:ℝ):=by
    rw [hex]
    exact completeCutoff_columns H b Btree cap D _ hb hD0.le hDH hn
  simpa only [hex] using deleted_row_complete_polynomial data u W H
    (Real.logb H (D/(j.absNorm:ℝ))) sigma freq b hH0 hW _ hbudget

end SevenEighths.DetectorDictionaryInverseRawInitialGates

end

end OAI

end Source2859

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialExcludedEnergy.lean; sha256: 51070863dc442d6655736179678ad4f129b8ff99853a703bbb540d0d6240ce13 -/
section Source2860
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedEnergy
open HeckeFamily HeckeDyadic InverseInitialExcludedPolynomial
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

def deletionWeight (χ:Character)(j:Ideal O):ℂ:=
  (moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ))

theorem deletionWeight_norm_le_one (χ:Character){j:Ideal O}(hj:j≠0):
    ‖deletionWeight χ j‖≤1 := by
  have hn:1≤(j.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj)
  have hp:0<(j.absNorm:ℝ):=lt_of_lt_of_le zero_lt_one hn
  have hw:‖(j.absNorm:ℂ)^(-(1/2:ℂ))‖≤1:=by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hp]
    apply Real.rpow_le_one_of_one_le_of_nonpos hn
    norm_num
  dsimp [deletionWeight]
  rw [norm_mul,norm_mul]
  calc
    _≤1*1:=mul_le_mul
      (by simpa only [one_mul] using (mul_le_mul (CubicEisenstein.norm_ideal_moebius_le_one j)
        (idealCoeff_norm_le_one χ j) (norm_nonneg _) zero_le_one)) hw
      (norm_nonneg _) (by positivity)
    _=1:=one_mul _

theorem marked_pointwise (χ:Character)(S:Finset (Ideal O))(hS:∀P∈S,Prime P)
    (W:ℝ→ℂ)(X σ t b:ℝ)(hX:0<X)(hW:∀x,W x≠0→x≤b)(mark:ℂ):
    ‖polynomial χ true W X σ t*mark‖^2≤
    ((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖^2 := by
  rw [inverse_polynomial_decomposition χ S hS W X σ t b hX hW,Finset.sum_mul]
  have hn:‖∑j∈idealDivisors (∏P∈S,P),
      ((moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ)))*
        polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖≤
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖:=by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro j hj
    change ‖deletionWeight χ j*polynomial _ _ _ _ _ _*mark‖≤_
    rw [mul_assoc,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    apply deletionWeight_norm_le_one χ
    exact ne_zero_of_dvd_ne_zero (prime_product_squarefree S hS).ne_zero
      ((mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj)
  have hh:=Finset.sum_mul_sq_le_sq_mul_sq (idealDivisors (∏P∈S,P))
    (fun _=>(1:ℝ)) (fun j=>‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr hn |>.trans
    hh

theorem marked_family {ι:Type*}(rows:Finset ι)(χ:ι→Character)
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(W:ℝ→ℂ)(X σ t b:ℝ)
    (hX:0<X)(hW:∀x,W x≠0→x≤b)(mark:ι→ℂ)(weight:ι→ℝ)
    (hw:∀u∈rows,0≤weight u):
    (∑u∈rows,weight u*‖polynomial (χ u) true W X σ t*mark u‖^2)≤
      ((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),∑u∈rows,weight u*
        ‖polynomial ((χ u).excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark u‖^2 := by
  calc
    _≤∑u∈rows,weight u*(((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial ((χ u).excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark u‖^2):=by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (marked_pointwise (χ u) S hS W X σ t b hX hW (mark u)) (hw u hu)
    _=_:=by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro u hu
      ring

end SevenEighths.InverseInitialExcludedEnergy

end

end OAI

end Source2860

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawInitialEnergy.lean; sha256: 6ff17a5d4c32007bd82bfe00effe6e8244fe87e8577d8fc6d3a429b8a3971584 -/
section Source2861
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseRawInitialEnergy
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRawDictionary InverseInitialExcludedPolynomial InverseInitialExcludedEnergy
open DetectorDictionaryInverseRawInitialGates CanonicalQuadraticSieve ConcreteTraceCRT
open ActualEisensteinCubic IdealMobiusDivisorSum CanonicalRowCompletion CanonicalCoefficientClass
local notation "O"=>HeckeFamily.O

private theorem admissible_one : Admissible (1:Ideal O) := by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

def initialFunction (data:RowData)(W:ℝ→ℂ)(H b Btree cap D sigma freq:ℝ)(j:Ideal O):O→ℂ:=
  originalTotalPolynomial
    (InitialMeanSquare.outsideSquarefreeIdeals (excluded data) (completeCutoff H b Btree cap))
    1 (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
    (twistedProfile W sigma freq) H (Real.logb H (D/(j.absNorm:ℝ))) 0

theorem deleted_rows_le_initial
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data:RowData)(W:ℝ→ℂ)(H D c b Btree cap sigma freq:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcapacity:D^(1+c)≤H)(hb:0≤b)
    (hW:∀x,W x≠0→x≤b)
    (j:Ideal O)(hj:j∈idealDivisors (∏P∈excluded data,P))
    (rows:Finset NonzeroElement)(hrows:∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H):
    (∑u∈rows,‖polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (D/(j.absNorm:ℝ)) sigma freq‖^2)
      ≤smoothedEnergy Φ H (initialFunction data W H b Btree cap D sigma freq j) := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (excluded data) (completeCutoff H b Btree cap)
  let f:=initialFunction data W H b Btree cap D sigma freq j
  have hFa:∀I∈F,Admissible I:=InitialMeanSquare.outsideSquarefree_admissible _ _
    (reflectionExcludedPrimes_bad (basePeriod data))
  have hs:Summable (fun u:O=>radialWeight Φ H u*‖f u‖^2):=
    (original_smoothed_overlap_triangle F admissible_one
      (fun I hI _=>admissible_supported (hFa I hI))
      (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) (twistedProfile W sigma freq)
      (zero_lt_one.trans hH) (Real.logb H (D/(j.absNorm:ℝ))) 0 (fun _=>0)
      Φ (fun x _=>hΦ x) (zero_lt_one.trans hH)).1
  have he (u:NonzeroElement)(hu:u∈rows):
      ‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W (D/(j.absNorm:ℝ)) sigma freq‖^2=
        radialWeight Φ H u.val*‖f u.val‖^2:=by
    have hn:‖eisEmbedding u.val‖^2/H∈Set.Icc (0:ℝ) 1:=by
      refine ⟨div_nonneg (sq_nonneg _) (zero_lt_one.trans hH).le,?_⟩
      apply (div_le_one (zero_lt_one.trans hH)).mpr
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    rw [(raw_complete_pool data H D c b Btree cap hH hD hc hcapacity hb W hW).2 j hj u sigma freq]
    change ‖f u.val‖^2=(Φ (‖eisEmbedding u.val‖^2/H)).re*‖f u.val‖^2
    rw [hone _ hn,Complex.one_re,one_mul]
  calc
    _=∑u∈rows,radialWeight Φ H u.val*‖f u.val‖^2:=Finset.sum_congr rfl he
    _=∑u∈rows.image Subtype.val,radialWeight Φ H u*‖f u‖^2:=by
      rw [Finset.sum_image (fun a _ b _ hab=>Subtype.val_injective hab)]
    _≤∑'u:O,radialWeight Φ H u*‖f u‖^2:=hs.sum_le_tsum _
      (fun u _=>mul_nonneg (hΦ _) (sq_nonneg _))
    _=_:=rfl

theorem raw_rows_le_initial
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (data:RowData)(W:ℝ→ℂ)(H D c b Btree cap sigma freq:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcapacity:D^(1+c)≤H)(hb:0≤b)
    (hW:∀x,W x≠0→x≤b)
    (rows:Finset NonzeroElement)(hrows:∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H):
    (∑u∈rows,‖polynomial (data.character u) true W D sigma freq‖^2)≤
      ((idealDivisors (∏P∈excluded data,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded data,P),
          smoothedEnergy Φ H (initialFunction data W H b Btree cap D sigma freq j) := by
  have hd:=marked_family rows data.character (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data)) W D sigma freq b
    (zero_lt_one.trans_le hD) hW (fun _=>1) (fun _=>1) (by intros;norm_num)
  simp only [mul_one,one_mul] at hd
  apply hd.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  exact deleted_rows_le_initial Φ hΦ hone data W H D c b Btree cap sigma freq
    hH hD hc hcapacity hb hW j hj rows hrows

end SevenEighths.DetectorDictionaryInverseRawInitialEnergy

end

end OAI

end Source2861

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawConjugateGates.lean; sha256: f707928da4d745a99bda52f5842be3bce13975892dd879541d618eb044ce9b5a -/
section Source2862
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawConjugateGates
open CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRayAttachment InverseInitialExcludedPeriod CanonicalCoefficientClass
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPool
open InverseInitialExcludedOverlap InverseMoment InverseInitialProfile
local notation "O"=>HeckeFamily.O

theorem conjugate_element_apply (η:Ideal O→*ℂ)(x:O):
    elementCharacter (conjugateIdealCharacter η) x=star (elementCharacter η x):=rfl

theorem conjugate_element_factors (η:Ideal O→*ℂ)(Q:Ideal O)
    (h:FactorsModulo Q (elementCharacter η)):
    FactorsModulo Q (elementCharacter (conjugateIdealCharacter η)):=by
  intro x y hxy
  exact congrArg star (h x y hxy)

theorem conjugate_element_norm (η:Ideal O→*ℂ)(x:O):
    ‖elementCharacter (conjugateIdealCharacter η) x‖=‖elementCharacter η x‖:=by
  rw [conjugate_element_apply,norm_star]

theorem raw_conjugate_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (conjugateIdealCharacter
      (idealCoeff (deletedBase data)).toMonoidHom) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)):=by
  obtain ⟨hq,he,hn,hp⟩:=raw_base_gates data
  refine ⟨hq,he,?_,conjugate_element_factors _ _ hp⟩
  intro x
  rw [conjugate_element_norm]
  exact hn x

theorem raw_conjugate_zero_outside (data:RowData)(I:Ideal O)
    (hI:¬outside (excluded data) I):
    conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom I=0:=by
  change star (idealCoeff (deletedBase data) I)=0
  rw [show idealCoeff (deletedBase data) I=0 from
    deleted_zero_outside (InverseInitialDetectorSource.baseCharacter data)
      (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) I hI,star_zero]

theorem childLogTest_conjugate (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=childLogTest (fun x=>star (W x)) (-θ):=by
  funext x
  simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate]
  ring

theorem childLogTest_conjugate_norm (W:ℝ→ℂ)(θ x:ℝ):
    ‖childLogTest (fun x=>star (W x)) (-θ) x‖=‖W x‖:=by
  rw [InverseInitialProfileBounds.childLogTest_norm,norm_star]

theorem childLogTest_physical_profiles (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=clippedSource (fun x=>star (W x)) 1 (-θ) ∧
    childLogTest W θ=clippedSource W 1 θ:=by
  rw [childLogTest_conjugate]
  exact ⟨InverseInitialProfileBounds.childLogTest_eq_clipped _ _,
    InverseInitialProfileBounds.childLogTest_eq_clipped _ _⟩

end SevenEighths.DetectorDictionaryInverseRawConjugateGates

end

end OAI

end Source2862

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialExcludedForcing.lean; sha256: 467b525fe91f52766ca6e18d01871ad5c1e5f827d43897d764f9c68a14d3fadd -/
section Source2863
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedForcing
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing InverseInitialLargePool
open InverseInitialExcludedPool InverseInitialExcludedOverlap
open InverseInitialCommonTuples InverseInitialCommonTransform
local notation "O"=>ActualEisensteinCubic.O

theorem pool_product_outside (F E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (hF:∀I∈F,outside E I)(A:Finset (primePool F)):
    outside E (∏i∈A,i.val) := by
  intro Q hQ hd
  obtain ⟨i,hi,hQi⟩:=((hE Q hQ).dvd_finsetProd_iff (fun i:primePool F=>i.val)).mp hd
  obtain ⟨I,hIF,hfactor⟩:=mem_primePool_iff.mp i.property
  exact hF I hIF Q hQ (hQi.trans (dvd_of_mem_normalizedFactors hfactor))

theorem residual_excluded_forcing
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    {P j:Ideal O}(hP:Admissible P)(hj:j∣P)(hPE:outside E P)
    (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:columns (originalOutside (originalSource Z r b) E) P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(u:O):
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial (originalSource Z r b) P j η (fun _=>1) W Z r z G u=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if residual P j∣(∏i∈A,i.val) then
          residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [residual_filtered _ E hE hP.2.1 hj hPE η hη,
    residual_eq_large_input _ F hP hj hF hsub η (fun _=>1) W Z r z G u]
  simp only [one_mul]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he:=common_selector_window W Z r z G b hZ hW hP hj F hF A
  have hm:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator j)=rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j):=by
    congr 1
    funext i
    exact poolPrimary_span F hF i
  have hmem:((∏i∈A,i.val)∈columns (originalOutside (originalSource Z r b) E) P j)↔
      ((∏i∈A,i.val)∈columns (originalSource Z r b) P j):=by
    rw [columns_filter _ E hE hP.2.1 hj hPE,Finset.mem_filter]
    exact and_iff_left (pool_product_outside F E hE hFE A)
  dsimp only
  simp only [hm,hmem]
  linear_combination
    (supportMobius (fun i:primePool F=>Ideal.span {poolPrimary F i}) A *
      elementCharacter η (∏i∈A,poolPrimary F i) *
      star (finiteSquarefreeRow (fun i:primePool F=>Ideal.span {poolPrimary F i})
        (poolPrimary_good F hF) A u))*he

variable {κ:Type*}
theorem original_tuples_excluded_input
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (T:Finset κ)(P:κ→Ideal O)(j:Ideal O)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside E (P k))
    (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:tupleColumns (originalOutside (originalSource Z r b) E) T P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(a:κ→ℂ)(u:O) :
    let S := originalSource Z r b
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑k∈T,a k*residualNormalizedPolynomial S (P k) j η (fun _=>1) W Z r z G u)=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>∑k∈T,a k*(if residual (P k) j∣(∏i∈A,i.val) then
          residualOverlapWindow (P k) j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u := by
  intro S
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [input_finset_sum (poolPrimary F) (poolPrimary_good F hF)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [residual_excluded_forcing W Z r z G b hZ hW E hE (hP k hk) (hj k hk) (hPE k hk) F hF hFE
    (fun c hc=>hsub (Finset.mem_biUnion.mpr ⟨k,hk,hc⟩)) η hη u]
  ring

end SevenEighths.InverseInitialExcludedForcing

end

end OAI

end Source2863

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawInput.lean; sha256: 6414b80f468027bef17111ed8f6021dc15a3169b6504df0d203365a014f4359f -/
section Source2864
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawInput
open CompletedGauss
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open ConcreteTraceCRT FirstCauchyArithmetic SecondPassArithmetic IdealMobiusDivisorSum
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialConjugateEnergy
open InverseInitialPoissonBridge InverseInitialExcludedForcing InverseInitialExcludedPool
open UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

private theorem admissible_one : Admissible (1:Ideal O):=by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

theorem input_generator_one (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)
    (η:O→*ℂ)(H:Finset (primePool F)→ℂ)(u:O):
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ η
      (primaryGenerator (1:Ideal O)) 1 1 H u=
    inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ η 1 1 1 H u:=by
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he:(fun i:primePool F=>Ideal.span {poolPrimary F i})=(fun i=>i.val):=
    funext (poolPrimary_span F hF)
  have hm:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator (1:Ideal O))=1:=by
    rw [he]
    exact selected_mask F 1 admissible_one A isCoprime_one_right
  have ho:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A 1=1:=by
    simp [rowCoprimeMask,Ideal.IsPrime.one_notMem]
  simp only [hm,ho]

theorem complete_pool_selector (E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (Dpool:ℕ)(hbad:fixedBadPrimes⊆E)(W:ℝ→ℂ)(b Z r:ℝ)
    (hZ:0<Z)(hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ)):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    ∀A:Finset (primePool F),
      (if (∏i∈A,i.val)∈F then W (((∏i∈A,i.val).absNorm:ℝ)/Z^r) else 0)=
        W (((∏i∈A,i.val).absNorm:ℝ)/Z^r):=by
  intro F A
  by_cases hw:W (((∏i∈A,i.val).absNorm:ℝ)/Z^r)=0
  · simp only [hw,ite_self]
  have hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad
  have hprod:=InitialMeanSquare.poolProduct_admissible F hF A
  have hout:outside E (∏i∈A,i.val):=
    pool_product_outside F E hE
      (fun I hI=>(mem_outsideIdealsUpTo.mp (Finset.mem_filter.mp hI).1).2.2) A
  have hN:((∏i∈A,i.val).absNorm:ℝ)≤(Dpool:ℝ):=
    ((div_le_iff₀ (Real.rpow_pos_of_pos hZ r)).mp (hW _ hw)).trans hbudget
  have hmem:(∏i∈A,i.val)∈F:=by
    apply Finset.mem_filter.mpr
    refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,hout⟩,hprod.2.1⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hprod.1)
    · exact_mod_cast hN
  exact ite_eq_left hmem

theorem original_complete_star_input
    (E:Finset (Ideal O))(hE:∀P∈E,Prime P)(Dpool:ℕ)(hbad:fixedBadPrimes⊆E)
    (η:Ideal O→*ℂ)(W:ℝ→ℂ)(b Z r:ℝ)(hZ:0<Z)
    (hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ))(u:O):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    star (originalTotalPolynomial F 1 η (fun _=>1) W Z r 0 u)=
      ((Z^(-r/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (poolPrimary_good F hF)
        Finset.univ (elementCharacter (conjugateIdealCharacter η)) 1 1 1
        (initialTest (poolPrimary F) (fun _=>1) (fun x=>star (W x)) Z r) u:=by
  intro F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have he:=selected_conjugate_row F hF 1 admissible_one (fun _ _=>isCoprime_one_right)
    (conjugateIdealCharacter η) (fun I=>star (W ((I.absNorm:ℝ)/Z^r))) u
  dsimp only at he
  rw [input_generator_one F hF] at he
  have hselector:(fun A:Finset (primePool F)=>
      if (∏i∈A,i.val)∈F then star (W (((∏i∈A,i.val).absNorm:ℝ)/Z^r)) else 0)=
      initialTest (poolPrimary F) (fun _=>1) (fun x=>star (W x)) Z r:=by
    funext A
    rw [complete_pool_selector E hE Dpool hbad (fun x=>star (W x)) b Z r hZ
      (fun x hx=>hW x (by simpa only [star_ne_zero] using hx)) hbudget]
    simp only [initialTest,one_mul,InitialMeanSquare.poolPrimary_norm F hF]
    rfl
  rw [hselector] at he
  rw [←he]
  unfold originalTotalPolynomial
  have hscalar:star ((Z^(-r/2):ℝ):ℂ)=((Z^(-r/2):ℝ):ℂ):=by simp
  simp only [add_zero,map_one,mul_one,star_mul,star_sum,hscalar,
    conjugateIdealCharacter_apply,heckeIdealCharacter_apply]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [star_intCast]
  ring

theorem original_complete_child_norm
    (E:Finset (Ideal O))(hE:∀P∈E,Prime P)(Dpool:ℕ)(hbad:fixedBadPrimes⊆E)
    (η:Ideal O→*ℂ)(W:ℝ→ℂ)(b Z r t:ℝ)(hZ:0<Z)
    (hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ))(u:O):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    ‖originalTotalPolynomial F 1 η (fun _=>1) (InverseMoment.childLogTest W t) Z r 0 u‖^2=
      ‖((Z^(-r/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (poolPrimary_good F hF)
        Finset.univ (elementCharacter (conjugateIdealCharacter η)) 1 1 1
        (initialTest (poolPrimary F) (fun _=>1)
          (InverseMoment.childLogTest (fun x=>star (W x)) (-t)) Z r) u‖^2:=by
  intro F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hw:∀x,InverseMoment.childLogTest W t x≠0→x≤b:=by
    intro x hx
    exact hW x ((mul_ne_zero_iff.mp hx).1)
  have he:=original_complete_star_input E hE Dpool hbad η
    (InverseMoment.childLogTest W t) b Z r hZ hw hbudget u
  dsimp only at he
  rw [DetectorDictionaryInverseRawConjugateGates.childLogTest_conjugate] at he
  have hn:=congrArg (fun z:ℂ=>‖z‖^2) he
  simpa only [norm_star] using hn

end SevenEighths.DetectorDictionaryInverseRawInput

end

end OAI

end Source2864

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawRealRadial.lean; sha256: 7a9b421cd3d64466e9bf0676c0898d32e9856f9cd906aef21aa34bb866155b7f -/
section Source2865
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawRealRadial
open InverseInitialConjugateEnergy ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

theorem exists_real_raw_radial_majorant:
    ∃Φ:𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x,(Φ x).im=0) ∧
      (∀x∈Set.Icc (0:ℝ) 1,Φ x=1):=by
  have hsub:Set.Icc (0:ℝ) 1⊆Set.Ioo (-1) 2:=by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v:ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv:ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf:ContDiff ℝ ∞ f).pow 2)
  have hsupp:Function.support v⊆Set.Icc (-1) 2:=by
    intro x hx
    have hn:x∈Function.support f:=by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  have hvc:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x
    exact Complex.ofReal_im _
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

theorem smoothedEnergy_eq_complex_norm (Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hreal:∀x,(Φ x).im=0)
    (H:ℝ)(hH:0<H)(f:O→ℂ):
    smoothedEnergy Φ H f=
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/H)*(‖f u‖^2:ℝ)‖:=by
  rw [real_smoothed_sum_eq Φ (fun x _=>hreal x) hH,
    Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (smoothedEnergy_nonneg Φ (fun x _=>hΦ x) hH f)]

end SevenEighths.DetectorDictionaryInverseRawRealRadial

end

end OAI

end Source2865

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawFourier.lean; sha256: e0731bd1892d2f24dbfdc4bda8afaa01f32e1aaa168d8023da37287c8eb7d0cd -/
section Source2866
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace SevenEighths.DetectorDictionaryInverseRawFourier
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge InverseInitialRawDictionary
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier FourierBridge JointLogSeparation

private theorem child_cover (Wref : ℝ→ℂ) (b D : ℝ) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b) (s : ℝ) :
    ∀I : Ideal O,I≠0 → childLogTest Wref s ((I.absNorm:ℝ)/D)≠0 →
      I∈ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊ := by
  intro I hI hi
  apply finite_source_cover Wref D b hD hWref I hI
  intro hz
  exact hi (by simp [childLogTest,hz])

theorem polynomial_mode_integrable (χ : Character) (inv : Bool)
    (g : 𝓢(ℝ,ℂ)) (Wref : ℝ→ℂ) (b c θ D : ℝ) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b) :
    Integrable (fun v:ℝ=>density g (Real.log c) v*
      polynomial χ inv (childLogTest Wref (θ+v)) D 0 0) := by
  simp_rw [polynomial_eq_finite χ inv (childLogTest Wref (θ+_)) D 0 0
    (ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊) (child_cover Wref b D hD hWref _)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,Finset.mul_sum]
  apply integrable_finsetSum
  intro I hI
  convert fourier_phase_integrable g
    (Real.log c+Real.log ((I.absNorm:ℝ)/D))
    ((D:ℂ)^(-(1/2:ℂ))*coefficient χ inv I*Wref ((I.absNorm:ℝ)/D)*
      logPhase θ (Real.log ((I.absNorm:ℝ)/D))) using 1
  funext v
  simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
  ring

theorem polynomial_clipped_fourier (χ : Character) (inv : Bool)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c θ D : ℝ) (hc : 0<c) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b)
    (hagree : ∀y,0<y → Wref y*W (c*y)=W (c*y)) :
    polynomial χ inv (clippedTest W c θ) D 0 0=
      ∫v:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) v*
        polynomial χ inv (childLogTest Wref (θ+v)) D 0 0 := by
  let S:=ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊
  have hcover : ∀I : Ideal O,I≠0 → clippedTest W c θ ((I.absNorm:ℝ)/D)≠0 → I∈S := by
    intro I hI hi
    have hIp : 0<(I.absNorm:ℝ)/D:=div_pos (by exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))) hD
    apply finite_source_cover Wref D b hD hWref I hI
    intro hz
    have he:=hagree _ hIp
    rw [hz,zero_mul] at he
    exact hi (by simp [clippedTest,childLogTest,←he])
  rw [polynomial_eq_finite χ inv (clippedTest W c θ) D 0 0 S hcover]
  simp_rw [polynomial_eq_finite χ inv (childLogTest Wref (θ+_)) D 0 0 S
    (child_cover Wref b D hD hWref _)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,Finset.mul_sum]
  have hint (I : Ideal O) : Integrable (fun v:ℝ=>
      density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) v*
        ((D:ℂ)^(-(1/2:ℂ))*(coefficient χ inv I*childLogTest Wref (θ+v) ((I.absNorm:ℝ)/D)))) := by
    convert fourier_phase_integrable (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)
      (Real.log c+Real.log ((I.absNorm:ℝ)/D))
      ((D:ℂ)^(-(1/2:ℂ))*coefficient χ inv I*Wref ((I.absNorm:ℝ)/D)*
        logPhase θ (Real.log ((I.absNorm:ℝ)/D))) using 1
    funext v
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  rw [integral_finsetSum _ (fun I _=>hint I)]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hz : I=0
  · subst I
    simp only [coefficient_zero,zero_mul,mul_zero,integral_zero]
  have hIp : 0<(I.absNorm:ℝ)/D:=div_pos (by exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz))) hD
  rw [clipped_test_fourier W lo hi hlo hs hW Wref c θ _ hc hIp (hagree _ hIp),
    ←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  ring

end SevenEighths.DetectorDictionaryInverseRawFourier

end

end OAI

end Source2866

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawEnergy.lean; sha256: 5c8ed5e967fd98ce8e65808ac7ade110af40473c3bbfab763d00170866663af6 -/
section Source2867
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace SevenEighths.DetectorDictionaryInverseRawFourier
open HeckeFamily HeckeDyadic InverseMoment InverseInitialClippedColumns
open InverseInitialOverlapFourier FourierBridge HeckeInverseAmplification

theorem polynomial_clipped_energy {ι : Type*} (rows : Finset ι)
    (χ : ι→Character) (inv : Bool) (A : ι→ℂ)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c θ D E : ℝ) (J : ℕ) (hc : 0<c) (hD : 0<D) (hE : 0≤E)
    (hWref : ∀x,Wref x≠0 → x≤b)
    (hagree : ∀y,0<y → Wref y*W (c*y)=W (c*y))
    (he : ∀s, (∑i∈rows,‖polynomial (χ i) inv (childLogTest Wref s) D 0 0*A i‖^2)
      ≤E*(1+‖s‖)^(2*J)) :
    (∑i∈rows,‖polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i‖^2)≤
      E*(1+‖θ‖)^(2*J)*
        (∫v:ℝ,(1+‖v‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) v‖)^2 := by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  let B:=density g (Real.log c)
  let φ : rows→ℝ→ℂ:=fun i v=>polynomial (χ i) inv (childLogTest Wref (θ+v)) D 0 0*A i
  have hint (i : rows) : Integrable (fun v:ℝ=>B v*φ i v) := by
    simpa only [B,φ,mul_assoc] using
      (polynomial_mode_integrable (χ i) inv g Wref b c θ D hD hWref).mul_const (A i)
  have hbound (v : ℝ) : (∑i:rows,‖φ i v‖^2)≤
      (E*(1+‖θ‖)^(2*J))*((1+‖v‖)^J)^2 := by
    dsimp only [φ]
    rw [Finset.sum_coe_sort rows (fun i=>‖polynomial (χ i) inv (childLogTest Wref (θ+v)) D 0 0*A i‖^2)]
    apply (he (θ+v)).trans
    have hh : 1+‖θ+v‖≤(1+‖θ‖)*(1+‖v‖) := by
      have hn:=norm_add_le θ v
      nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg v)]
    calc
      _≤E*((1+‖θ‖)*(1+‖v‖))^(2*J):=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh _) hE
      _= _:=by rw [mul_pow,pow_mul];ring
  have hden : Integrable (fun v:ℝ=>(1+‖v‖)^J*‖B v‖) := by
    simpa only [B,density_norm] using AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hh:=CenteredMomentHeckeWindowEnergy.finite_weighted_integral_energy B φ
    (fun v:ℝ=>(1+‖v‖)^J) (by intro v;positivity)
    (E*(1+‖θ‖)^(2*J)) (by positivity) hden hint hbound
  have heq (i : rows) : (∫v:ℝ,B v*φ i v)=
      polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i := by
    rw [polynomial_clipped_fourier (χ i) inv W lo hi hlo hs hW Wref b c θ D hc hD hWref hagree,
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards with v
    dsimp [B,φ,g]
    ring
  simp_rw [heq] at hh
  rw [Finset.sum_coe_sort rows (fun i=>‖polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i‖^2)] at hh
  simpa only [B,density_norm,g] using hh

theorem rawMoment_reference (data : RowData)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c κ C : ℝ) (J : ℕ) (hC : 0≤C)
    (hWref : ∀x,Wref x≠0 → x≤b)
    (hagree : ∀y,0<y → Wref y*W y=W y)
    (he : ∀s,RawMoment data (childLogTest Wref s) c κ (C*(1+‖s‖)^(2*J))) :
    RawMoment data W c κ
      (C*(∫v:ℝ,(1+‖v‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) v‖)^2) := by
  intro H D hH hD hHD rows hrows
  have hh:=polynomial_clipped_energy rows data.character true (fun _=>1)
    W lo hi hlo hs hW Wref b 1 0 D (C*H*(H*max 1 D)^κ) J (by norm_num) hD
    (by positivity) hWref (by simpa only [one_mul] using hagree) (by
      intro s
      have hb:=he s H D hH hD hHD rows hrows
      simpa only [mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using hb)
  have heq : clippedTest W 1 0=W := by
    funext x
    simp [clippedTest,childLogTest,logPhase]
  rw [heq] at hh
  simpa only [mul_one,one_mul,norm_zero,add_zero,one_pow,mul_assoc,mul_left_comm,mul_comm] using hh

end SevenEighths.DetectorDictionaryInverseRawFourier

end

end OAI

end Source2867

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawCompact.lean; sha256: 187dd0f0114c1693d264f45f5756b259570abd971fb726657770375c01278268 -/
section Source2868
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseRawCompact
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment FourierBridge HeckePrimeAnnular
open CenteredMomentOriginalReflectionErrorMass CenteredMomentCounting
open ActualEisensteinCubic ConcreteTraceCRT

local notation "O" => HeckeFamily.O

lemma inverse_polynomial_all_ideals (χ : Character) (W : ℝ→ℂ) (D freq : ℝ) :
    polynomial χ true W D 0 freq =
      (D:ℂ)^(-(1/2:ℂ))*∑'I:Ideal O,coefficient χ true I*annularWeight W D 0 freq I := by
  unfold polynomial
  congr 1
  have he : (∑'I:HeckeDyadic.NonzeroIdeal,coefficient χ true I.val*annularWeight W D 0 freq I.val)=
      ∑'I:Ideal O,coefficient χ true I*annularWeight W D 0 freq I := by
    apply tsum_subtype_eq_of_support_subset (s:={I:Ideal O|I≠0})
      (f:=fun I:Ideal O=>coefficient χ true I*annularWeight W D 0 freq I)
    intro I hI hz
    subst I
    exact hI (by simp only [coefficient_zero,zero_mul])
  simpa only [summand,HeckeDyadic.norm,annularWeight,mul_assoc] using he

theorem inverse_polynomial_bound (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖polynomial χ true W D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  rw [inverse_polynomial_all_ideals]
  apply normalized_linear_bound D _ hD
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>coefficient χ true I*annularWeight W D 0 freq I)
    (max 1 b*D) B (by positivity) hB (by
      change coefficient χ true (0:Ideal O)*_ = 0
      rw [coefficient_zero,zero_mul])
    (by
      intro I
      by_cases hI:I=0
      · subst I
        simpa only [coefficient_zero,zero_mul,norm_zero] using hB
      rw [norm_mul,annularWeight_zero_norm W D freq hD I hI]
      exact (mul_le_mul (coefficient_norm_le χ true I) (hW _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul B))
    (by
      intro I hne
      have hw : W ((I.absNorm:ℝ)/D)≠0 := by
        intro hz
        exact hne (by simp only [annularWeight,hz,zero_mul,mul_zero])
      exact ((div_le_iff₀ hD).mp (hs hw)).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le))
  convert hh using 1; ring

lemma childLogTest_norm (W : ℝ→ℂ) (s x : ℝ) :
    ‖childLogTest W s x‖=‖W x‖ := by
  simp only [childLogTest,norm_mul,logPhase_norm,mul_one]

theorem inverse_reference_bound (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃A:ℝ,0<A ∧ ∀(χ:Character) (s D:ℝ),0<D →
      ‖polynomial χ true (childLogTest W s) D 0 0‖≤A*Real.sqrt D := by
  obtain ⟨B,hB,hbound⟩:=compact_norm_bound W a b ha hs W.continuous
  refine ⟨128*max 1 b*B,by positivity,?_⟩
  intro χ s D hD
  apply inverse_polynomial_bound χ (childLogTest W s) b B D 0 hB.le hD
  · intro x
    simpa only [childLogTest_norm] using hbound x
  · intro x hx
    have hw : W x≠0 := by
      intro hz
      exact hx (by simp only [childLogTest,hz,zero_mul])
    exact (hs hw).2

theorem nonzero_element_rows_card (rows : Finset NonzeroElement) (H : ℝ) (hH : 1≤H)
    (hrows : ∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) :
    (rows.card:ℝ)≤128*H := by
  have hh:=DescentFiberCost.finite_element_count_real (rows.image Subtype.val) H hH (by
    intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hrows v hv)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

theorem reference_energy_linear (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃K:ℝ,0<K ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D:ℝ),1≤H → 0<D →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤K*H*D := by
  obtain ⟨A,hA,hbound⟩:=inverse_reference_bound W a b ha hs
  refine ⟨128*A^2,by positivity,?_⟩
  intro χ rows s H D hH hD hrows
  calc
    _≤∑v∈rows,A^2*D := by
      apply Finset.sum_le_sum
      intro v _
      have hh:=pow_le_pow_left₀ (norm_nonneg _) (hbound (χ v) s D hD) 2
      simpa only [mul_pow,Real.sq_sqrt hD.le] using hh
    _=(rows.card:ℝ)*(A^2*D) := by simp
    _≤(128*H)*(A^2*D) := mul_le_mul_of_nonneg_right
      (nonzero_element_rows_card rows H hH hrows) (by positivity)
    _=(128*A^2)*H*D := by ring

theorem subunit_rows_reference_energy (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃C0:ℝ,0<C0 ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D:ℝ),1≤H → 0<D → D≤1 →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤C0*H := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K,hK,?_⟩
  intro χ rows s H D hH hD hD1 hrows
  exact (hbound χ rows s H D hH hD hrows).trans
    (mul_le_of_le_one_right (by positivity) hD1)

lemma scale_le_rows (c H D : ℝ) (hc : 0≤c) (hH : 1≤H)
    (_hD : 0<D) (hDH : D^(1+c)≤H) : D≤H := by
  by_cases hD1:D≤1
  · exact hD1.trans hH
  · have hd : 1≤D := le_of_not_ge hD1
    calc
      D=D^(1:ℝ) := (Real.rpow_one D).symm
      _≤D^(1+c) := Real.rpow_le_rpow_of_exponent_le hd (by linarith)
      _≤H := hDH

theorem small_rows_reference_energy (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D c:ℝ),1≤H → H≤H0 → 0≤c → 0<D → D^(1+c)≤H →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤C0*H := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K*H0,by positivity,?_⟩
  intro χ rows s H D c hH hHH0 hc hD hDH hrows
  calc
    _≤K*H*D := hbound χ rows s H D hH hD hrows
    _≤K*H*H0 := mul_le_mul_of_nonneg_left ((scale_le_rows c H D hc hH hD hDH).trans hHH0)
      (by positivity)
    _=(K*H0)*H := by ring

lemma raw_majorant_ge_linear (C C0 H D κ s : ℝ) (J : ℕ)
    (hC : 0≤C) (hC0 : 0≤C0) (hH : 1≤H) (hκ : 0≤κ) :
    C0*H≤((C+C0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
  have ht : 1≤(1+‖s‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg s])
  have hb : 1≤H*max 1 D := hH.trans
    (le_mul_of_one_le_right (by positivity) (le_max_left _ _))
  have hp : 1≤(H*max 1 D)^κ := Real.one_le_rpow hb hκ
  calc
    C0*H≤(C+C0)*H := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _≤((C+C0)*(1+‖s‖)^(2*J))*H := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity) ht) (by positivity)
    _≤_ := le_mul_of_one_le_right (by positivity) hp

theorem rawMoment_of_large_rows_ge_one (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(data:RowData) (c κ C:ℝ) (J:ℕ),
      0≤c → 0≤κ → 0≤C →
      (∀(s H D:ℝ),H0≤H → 1≤D → D^(1+c)≤H →
        ∀rows:Finset NonzeroElement,
          (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
          (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
            (C*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ) →
      ∀s:ℝ,RawMoment data (childLogTest W s) c κ ((C+C0)*(1+‖s‖)^(2*J)) := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K*H0,by positivity,?_⟩
  intro data c κ C J hc hκ hC hlarge s H D hH hD hDH rows hrows
  have hsmall (hDH0:D≤H0) :
      (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
        ((C+K*H0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
    calc
      _≤K*H*D := hbound data.character rows s H D hH hD hrows
      _≤K*H*H0 := mul_le_mul_of_nonneg_left hDH0 (by positivity)
      _=(K*H0)*H := by ring
      _≤_ := raw_majorant_ge_linear C (K*H0) H D κ s J hC (by positivity) hH hκ
  by_cases hHH0:H≤H0
  · exact hsmall ((scale_le_rows c H D hc hH hD hDH).trans hHH0)
  by_cases hD1:D≤1
  · exact hsmall (hD1.trans hH0)
  · apply (hlarge s H D (le_of_not_ge hHH0) (le_of_not_ge hD1) hDH rows hrows).trans
    gcongr
    exact le_add_of_nonneg_right (by positivity)

theorem rawMoment_of_large_rows (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(data:RowData) (c κ C:ℝ) (J:ℕ),
      0≤c → 0≤κ → 0≤C →
      (∀(s H D:ℝ),H0≤H → 0<D → D^(1+c)≤H →
        ∀rows:Finset NonzeroElement,
          (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
          (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
            (C*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ) →
      ∀s:ℝ,RawMoment data (childLogTest W s) c κ ((C+C0)*(1+‖s‖)^(2*J)) := by
  obtain ⟨C0,hC0,hcomplete⟩:=rawMoment_of_large_rows_ge_one W a b ha hs H0 hH0
  refine ⟨C0,hC0,?_⟩
  intro data c κ C J hc hκ hC hlarge
  apply hcomplete data c κ C J hc hκ hC
  intro s H D hH hD hDH rows hrows
  exact hlarge s H D hH (zero_lt_one.trans_le hD) hDH rows hrows

end SevenEighths.DetectorDictionaryInverseRawCompact

end

end OAI

end Source2868

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawReference.lean; sha256: 72ba8916857bb07d0420518975cc1393facbd958b36932a13a0ef0e3ef28d0d1 -/
section Source2869
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialExcludedPeriod
open InverseInitialRayAttachment InverseInitialProfileBounds
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawInitialEnergy
open DetectorDictionaryInverseRawInput DetectorDictionaryInverseRawInputBound
open DetectorDictionaryInverseRawConjugateGates DetectorDictionaryInverseRawRealRadial
open DetectorDictionaryInverseRawGeometry IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

theorem raw_reference_large (W:𝓢(ℝ,ℂ))(a b c κ:ℝ)(ha:0<a)(hb:0<b)
    (hs:Function.support W⊆Set.Icc a b)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C H₀:ℝ,0<C ∧ 1<H₀ ∧
      ∀(t H D:ℝ),H₀≤H→1≤D→D^(1+c)≤H→∀rows:Finset NonzeroElement,
      (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H)→
      (∑u∈rows,‖polynomial (data.character u) true (childLogTest W t) D 0 0‖^2)≤
        (C*(1+‖t‖)^(2*J))*H*(H*max 1 D)^κ := by
  obtain ⟨Φ,hΦcompact,hΦ,hreal,hone⟩:=exists_real_raw_radial_majorant
  obtain ⟨η,τ,π,eps,hη,hτ,hπ,heps,hηone,hηgap,hτgap,hcost⟩:=
    raw_fixed_reserves c (κ/2) hc (by positivity)
  let gap:=capacityGap c/4
  have hgap:0<gap:=by dsimp [gap];exact div_pos (capacityGap_pos c hc) (by norm_num)
  have hηsmall:η≤gap/50:=by dsimp [gap];nlinarith
  have hτsmall:τ≤gap/50:=by dsimp [gap];nlinarith
  let Wbar:=SecondPassIntegration.conjugateProfile W
  have hsbar:Function.support Wbar⊆Set.Icc a b:=by
    intro x hx
    exact hs (by simpa only [Wbar,Function.mem_support,SecondPassIntegration.conjugateProfile_apply,star_ne_zero] using hx)
  obtain ⟨J,Btree,hBtree,hinput⟩:=raw_input_bound Wbar a b ha hsbar Φ
    gap eps π η τ (κ/4) hgap heps hπ hη hηone hηsmall hτ hτsmall (by positivity)
  refine ⟨J,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩:=raw_conjugate_base_gates data
  obtain ⟨C,Hq,hC,hHq,hinput⟩:=hinput (deletedPeriod (basePeriod data)) hq
  obtain ⟨Hg,hg⟩:=eventually_atTop.mp (shifted_raw_geometry_eventually data c η hc hη)
  let T:=idealDivisors (∏P∈excluded data,P)
  let Ctotal:=((T.card:ℝ)+1)^2*C
  refine ⟨Ctotal,max Hq Hg,by dsimp [Ctotal];positivity,lt_max_of_lt_left hHq,?_⟩
  intro t H D hH hD hcapacity rows hrows
  have hHq':Hq≤H:=(le_max_left _ _).trans hH
  obtain ⟨hHp,hgeom⟩:=hg H ((le_max_right _ _).trans hH)
  have hHpos:0<H:=zero_lt_one.trans hHp
  have hWt:∀x,childLogTest W t x≠0→x≤b:=by
    intro x hx
    exact (hs ((mul_ne_zero_iff.mp hx).1)).2
  have hraw:=raw_rows_le_initial Φ hΦ hone data (childLogTest W t) H D c b Btree 2 0 0
    hHp hD hc hcapacity hb.le hWt rows hrows
  have hterm (j:Ideal O)(hj:j∈T):
      smoothedEnergy Φ H (initialFunction data (childLogTest W t) H b Btree 2 D 0 0 j)≤
        C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
    obtain ⟨hrlo,hr₁,hr₂,hex,hrcap,hDH⟩:=hgeom D hD hcapacity j hj
    let r:=Real.logb H (D/(j.absNorm:ℝ))
    let Dpool:=completeCutoff H b Btree 2
    have hpool:Btree*H^3≤(Dpool:ℝ):=by
      convert completeCutoff_tree H b Btree 2 using 1 ; norm_num
    have hbcover:b*H^r≤(Dpool:ℝ):=by
      rw [hex]
      exact completeCutoff_columns H b Btree 2 D _ hb.le (zero_lt_one.trans_le hD).le hDH
        (excluded_divisor_norm data j hj).1
    have hbound:=hinput H hHq' Dpool hpool
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom))
      hn hperiod r (-t) (by dsimp [r];linarith)
      (by dsimp [gap] at *;linarith [(capacityGap_pos c hc).le])
      (by dsimp [gap] at *;linarith [(capacityGap_pos c hc).le])
      (by have hh:=capacityGap_lt_one c hc;linarith)
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
      (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data)))
    let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by
      rw [poolPrimary_span F hF i];infer_instance
    have hf:initialFunction data (childLogTest W t) H b Btree 2 D 0 0 j=
        originalTotalPolynomial F 1 (idealCoeff (deletedBase data)).toMonoidHom
          (fun _=>1) (childLogTest W t) H r 0:=by
      unfold initialFunction
      dsimp only [F]
      rw [hqset]
      congr 1
      funext x
      simp [twistedProfile,HeckeDyadic.shift]
    rw [hf,smoothedEnergy_eq_complex_norm Φ hΦ hreal H hHpos]
    have he: (∑'u:O,Φ (‖eisEmbedding u‖^2/H)*
        (‖originalTotalPolynomial F 1 (idealCoeff (deletedBase data)).toMonoidHom
          (fun _=>1) (childLogTest W t) H r 0 u‖^2:ℝ))=
        (∑'u:O,Φ (‖eisEmbedding u‖^2/H)*
        (‖((H^(-r/2):ℝ):ℂ)*SecondPassArithmetic.inputConjugateRow
          (poolPrimary F) (poolPrimary_good F (InitialMeanSquare.outsideSquarefree_admissible
            (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
            (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data)))))
          Finset.univ (elementCharacter (conjugateIdealCharacter
            (idealCoeff (deletedBase data)).toMonoidHom)) 1 1 1
          (initialTest (poolPrimary F) (fun _=>1) (childLogTest Wbar (-t)) H r) u‖^2:ℝ)):=by
      apply tsum_congr
      intro u
      congr 2
      exact original_complete_child_norm (reflectionExcludedPrimes (deletedPeriod (basePeriod data)))
        (reflectionExcludedPrimes_prime (deletedPeriod (basePeriod data))) Dpool
        (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data))) _ W b H r t hHpos
        (fun x hx=>(hs hx).2) hbcover u
    rw [he]
    simpa only [norm_neg] using hbound
  apply hraw.trans
  calc
    _≤(T.card:ℝ)*∑j∈T,C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg _)
    _=(T.card:ℝ)^2*C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _≤Ctotal*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
      dsimp [Ctotal]
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) T.card]
    _≤(Ctotal*(1+‖t‖)^(2*J))*H*(H*max 1 D)^κ:=by
      have he:15*η+π+eps+κ/4≤κ:=by linarith
      have hh:=raw_output_budget H D κ (15*η+π+eps+κ/4) hHp.le hκ.le he
      rw [show (1+15*η+π+eps+κ/4:ℝ)=1+(15*η+π+eps+κ/4) by ring]
      nlinarith [mul_le_mul_of_nonneg_left hh
        (show 0≤Ctotal*(1+‖t‖)^(2*J) by dsimp [Ctotal];positivity)]

theorem raw_reference_moment (W:𝓢(ℝ,ℂ))(a b c κ:ℝ)(ha:0<a)(hb:0<b)
    (hs:Function.support W⊆Set.Icc a b)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C:ℝ,0<C ∧ ∀t:ℝ,
      RawMoment data (childLogTest W t) c κ (C*(1+‖t‖)^(2*J)) := by
  obtain ⟨J,hlarge⟩:=raw_reference_large W a b c κ ha hb hs hc hκ
  refine ⟨J,?_⟩
  intro data
  obtain ⟨C,H₀,hC,hH₀,hlarge⟩:=hlarge data
  obtain ⟨C₀,hC₀,hcomplete⟩:=DetectorDictionaryInverseRawCompact.rawMoment_of_large_rows_ge_one
    W a b ha hs H₀ hH₀.le
  refine ⟨C+C₀,add_pos hC hC₀,?_⟩
  exact hcomplete data c κ C J hc.le hκ.le hC.le hlarge

end SevenEighths.DetectorDictionaryInverseRawReference

end

end OAI

end Source2869

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseUniformLog.lean; sha256: 759d1f8f4234c3071ee76f234dc7384a7bdc37c6765bf85e696a67602131e25b -/
section Source2870
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial CenteredMomentDetectorDictionary

lemma logTest_apply (W : ℝ→ℂ) (n : ℕ) (x : ℝ) :
    logTest W n x=(Real.log x:ℂ)^n*W x := by
  induction n with
  | zero => simp [logTest]
  | succ n ih => simp only [logTest,logProfile,ih,pow_succ];ring

def baseProfile (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R : ℝ) : ℝ→ℂ :=
  logTest (orientedProfile reverse (ratioProfile V W R)) n

lemma baseProfile_support (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R : ℝ) :
    Function.support (baseProfile reverse n V W R)⊆Function.support W := by
  apply (logTest_support _ _).trans
  cases reverse
  · exact ratioProfile_support V W R
  · rw [orientedProfile,ite_eq_left rfl,conjugate_profile_support]
    exact ratioProfile_support V W R

lemma baseProfile_smooth (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R a b : ℝ)
    (ha : 0<a) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Icc a b) : ContDiff ℝ ∞ (baseProfile reverse n V W R) := by
  apply logTest_smooth _ n a b ha
  · cases reverse
    · exact (ratioProfile_support V W R).trans hs
    · rw [orientedProfile,ite_eq_left rfl,conjugate_profile_support]
      exact (ratioProfile_support V W R).trans hs
  · have hv : ContDiff ℝ ∞ (ratioProfile V W R) :=
      (hV.comp (by fun_prop)).mul hW
    cases reverse
    · exact hv
    · exact conjugate_profile_smooth _ hv

def inverseLogFamily (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) : ℂ :=
  Real.exp (-p.1*x) • ((x:ℂ)^n*
    (orientedProfile reverse V (p.2*Real.exp x)*orientedProfile reverse W (Real.exp x)))

lemma inverseLogFamily_smooth (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (inverseLogFamily reverse n V W)) := by
  have hv : ContDiff ℝ ∞ (orientedProfile reverse V) := by
    cases reverse
    · exact hV
    · exact conjugate_profile_smooth _ hV
  have hw : ContDiff ℝ ∞ (orientedProfile reverse W) := by
    cases reverse
    · exact hW
    · exact conjugate_profile_smooth _ hW
  unfold inverseLogFamily Function.uncurry
  exact (by fun_prop : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=>Real.exp (-p.1.1*p.2))).smul
    (((Complex.ofRealCLM.contDiff.comp (contDiff_snd : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=>p.2))).pow n).mul
      ((hv.comp (by fun_prop)).mul (hw.comp (by fun_prop))))

lemma inverseLogFamily_eq (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) :
    inverseLogFamily reverse n V W p x=realInterpolatedLog (baseProfile reverse n V W p.2) p x := by
  unfold inverseLogFamily realInterpolatedLog baseProfile
  rw [logTest_apply,Real.log_exp]
  cases reverse <;> simp [orientedProfile,ratioProfile,map_mul]

lemma inverseLogFamily_support (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (inverseLogFamily reverse n V W p)⊆Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  have he : inverseLogFamily reverse n V W p=realInterpolatedLog (baseProfile reverse n V W p.2) p :=
    funext (inverseLogFamily_eq reverse n V W p)
  rw [he]
  exact realInterpolatedLog_support _ a b ha ((baseProfile_support reverse n V W p.2).trans hs) p

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI

end Source2870

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseUniformFamily.lean; sha256: b73d146afebb23a99e212c826e612fd6933f54ecb895a9713f71035c564c2af5 -/
section Source2871
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic JointLogSeparation CenteredMomentDetectorDictionary

def inverseLogSchwartz (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (p : ℝ×ℝ) : 𝓢(ℝ,ℂ) :=
  realInterpolatedLogSchwartz (baseProfile reverse n V W p.2) a b ha
    ((baseProfile_support reverse n V W p.2).trans hs)
    (baseProfile_smooth reverse n V W p.2 a b ha hV hW hs) p

lemma inverseLogSchwartz_apply (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (p : ℝ×ℝ) (x : ℝ) :
    inverseLogSchwartz reverse n V W a b ha hV hW hs p x=inverseLogFamily reverse n V W p x := by
  rw [inverseLogSchwartz,realInterpolatedLogSchwartz_apply,inverseLogFamily_eq]

def inverseSchwartz (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  interpolatedProfile (baseProfile reverse n V W R) a b ha
    ((baseProfile_support reverse n V W R).trans hs)
    (baseProfile_smooth reverse n V W R a b ha hV hW hs) σ t

lemma inverseSchwartz_apply (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (R σ t x : ℝ) :
    inverseSchwartz reverse n V W a b ha hV hW hs R σ t x=
      twistProfile (baseProfile reverse n V W R) σ t x :=
  interpolatedProfile_apply _ _ _ _ _ _ _ _ _

theorem inverseSchwartz_operator_uniform (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Icc a b) (Rmax : ℝ)
    (op : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ)) (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀R∈Icc (0:ℝ) Rmax,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (op (inverseSchwartz reverse n V W a b ha hV hW hs R σ t))≤C*(1+‖t‖)^J := by
  obtain ⟨T,A,hA,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (op.comp (CompletedHeight.fixedLogReturnCLM a b ha)) S
  obtain ⟨J,B,hB,hbound⟩ := compact_family_frequencyTwist
    (inverseLogFamily reverse n V W) (inverseLogFamily_smooth reverse n V W hV hW)
    (|Real.log a|+|Real.log b|) (by positivity) (inverseLogFamily_support reverse n V W a b ha hs)
    (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) Rmax) (isCompact_Icc.prod isCompact_Icc)
    (inverseLogSchwartz reverse n V W a b ha hV hW hs)
    (inverseLogSchwartz_apply reverse n V W a b ha hV hW hs) T
  refine ⟨J,A*B,mul_pos hA hB,?_⟩
  intro R hR σ hσ t
  have hp : (σ,R)∈Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) Rmax := ⟨hσ,hR⟩
  have hheight : ‖t/(2*Real.pi)‖≤‖t‖ := by
    rw [norm_div,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])
  have hh := hcontrol (frequencyTwist (inverseLogSchwartz reverse n V W a b ha hV hW hs (σ,R)) (t/(2*Real.pi)))
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (op (inverseSchwartz reverse n V W a b ha hV hW hs R σ t))≤_ at hh
  apply hh.trans
  have hb : T.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (inverseLogSchwartz reverse n V W a b ha hV hW hs (σ,R)) (t/(2*Real.pi)))≤B*(1+‖t‖)^J :=
    (hbound (σ,R) hp (t/(2*Real.pi))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) J) hB.le)
  exact (mul_le_mul_of_nonneg_left hb hA.le).trans_eq (by ring)

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI

end Source2871

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseUniformTests.lean; sha256: 196e776c64e0c63cd48a9d818c218974e3f7713adbc623e81c2442f83d03a8f6 -/
section Source2872
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

def sourceOperator (scaled : Bool) : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  if scaled then scaleCLM else ContinuousLinearMap.id ℝ _

def inverseDetectorSchwartz (reverse : Bool) (n : ℕ) (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  inverseSchwartz reverse n cutoff positiveAnnular (1/4) (9/4) (by norm_num)
    (cutoff.smooth ⊤) positiveAnnular_smooth positiveAnnular_support R σ t

lemma inverseDetectorSchwartz_apply (reverse : Bool) (n : ℕ) (R σ t x : ℝ) :
    inverseDetectorSchwartz reverse n R σ t x=
      twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t x :=
  inverseSchwartz_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _

def inverseDetectorTest (scaled reverse : Bool) (n : ℕ) (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  sourceOperator scaled (inverseDetectorSchwartz reverse n R σ t)

lemma inverseDetectorTest_apply (scaled reverse : Bool) (n : ℕ) (R σ t x : ℝ) :
    inverseDetectorTest scaled reverse n R σ t x=
      if scaled then scaleProfile (twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t) x
      else twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t x := by
  have he : (inverseDetectorSchwartz reverse n R σ t : ℝ→ℂ)=
      twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t :=
    funext (inverseDetectorSchwartz_apply reverse n R σ t)
  cases scaled
  · exact inverseDetectorSchwartz_apply _ _ _ _ _ _
  · change scaleCLM (inverseDetectorSchwartz reverse n R σ t) x=_
    rw [scaleCLM_apply,he]
    rfl

theorem inverseDetectorTest_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀R∈Icc (0:ℝ) 4,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤C*(1+‖t‖)^J := by
  choose degree C hC hb using fun q : Bool×Bool×Fin 3=>inverseSchwartz_operator_uniform
    q.2.1 q.2.2.val cutoff positiveAnnular (1/4) (9/4) (by norm_num)
    (cutoff.smooth ⊤) positiveAnnular_smooth positiveAnnular_support 4 (sourceOperator q.1) S
  let J := (Finset.univ : Finset (Bool×Bool×Fin 3)).sup degree
  have hsum : 0≤∑q : Bool×Bool×Fin 3,C q := Finset.sum_nonneg (fun q _=>(hC q).le)
  refine ⟨J,1+∑q : Bool×Bool×Fin 3,C q,by linarith,?_⟩
  intro scaled reverse n hn R hR σ hσ t
  let q : Bool×Bool×Fin 3 := (scaled,reverse,⟨n,by omega⟩)
  have hCq : C q≤1+∑q : Bool×Bool×Fin 3,C q := by
    have hh := Finset.single_le_sum (fun q (_ : q∈(Finset.univ : Finset (Bool×Bool×Fin 3)))=>(hC q).le) (Finset.mem_univ q)
    linarith
  have hdegree : degree q≤J := Finset.le_sup (Finset.mem_univ q)
  have he := hb q R hR σ hσ t
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤_ at he
  exact he.trans (mul_le_mul hCq (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree)
    (by positivity) (by linarith))

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI

end Source2872

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseUniformSource.lean; sha256: b3fddbbb0ffd420c5dd5ae3f1e6eed6e90452c6e1193ce09153dd90ba0787c3a -/
section Source2873
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial

lemma positiveAnnular_support_sharp : Function.support positiveAnnular⊆Ioo (1/2) 2 := by
  intro x hx
  have hx0 : 0≤x := by have := (positiveAnnular_support hx).1; linarith
  have he : DyadicTransfer.annularCutoff cutoff x≠0 := by
    rwa [←positiveAnnular_eq x hx0]
  simpa using HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx0 0 (by simpa using he)

lemma ratioProfile_zero_of_four_le (R : ℝ) (hR : 4≤R) :
    ratioProfile cutoff positiveAnnular R=0 := by
  funext x
  by_cases hx : positiveAnnular x=0
  · simp [ratioProfile,hx]
  · have hs := positiveAnnular_support_sharp hx
    have hrx : 2≤R*x := by nlinarith [hs.1]
    simp [ratioProfile,cutoff_zero _ hrx]

lemma inverseDetectorTest_zero_of_four_le (scaled reverse : Bool) (n : ℕ) (R σ t : ℝ)
    (hR : 4≤R) : inverseDetectorTest scaled reverse n R σ t=0 := by
  have hz : inverseDetectorSchwartz reverse n R σ t=0 := by
    ext x
    rw [inverseDetectorSchwartz_apply]
    simp only [baseProfile,ratioProfile_zero_of_four_le R hR]
    cases reverse <;> simp [orientedProfile,twistProfile,HeckeDyadic.shift,logTest_apply]
  rw [inverseDetectorTest,hz,map_zero]

theorem inverseDetectorTest_uniform_all_ratios (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀R : ℝ,0≤R→∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤C*(1+‖t‖)^J := by
  obtain ⟨J,C,hC,hb⟩ := inverseDetectorTest_uniform S
  refine ⟨J,C,hC,?_⟩
  intro scaled reverse n hn R hR σ hσ t
  by_cases hh : R≤4
  · exact hb scaled reverse n hn R ⟨hR,hh⟩ σ hσ t
  · rw [inverseDetectorTest_zero_of_four_le _ _ _ _ _ _ (le_of_not_ge hh),map_zero]
    positivity

def inverseSourceSchwartz (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  inverseDetectorTest scaled reverse n (U^r/U^tstar) σ t

lemma inverseSourceSchwartz_apply (scaled reverse : Bool) (n : ℕ) (U tstar r σ t x : ℝ) :
    inverseSourceSchwartz scaled reverse n U tstar r σ t x=
      if scaled then scaleProfile (twistProfile
        (logTest (orientedProfile reverse (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t) x
      else twistProfile
        (logTest (orientedProfile reverse (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t x := by
  simp only [inverseSourceSchwartz,inverseDetectorTest_apply,baseProfile,
    HeckeDetectorInverseFiberCount.inverseTest,inverseProfile_eq_ratio]

theorem inverseSourceSchwartz_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀U : ℝ,0<U→∀tstar r : ℝ,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseSourceSchwartz scaled reverse n U tstar r σ t)≤C*(1+‖t‖)^J := by
  obtain ⟨J,C,hC,hb⟩ := inverseDetectorTest_uniform_all_ratios S
  refine ⟨J,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t
  exact hb scaled reverse n hn (U^r/U^tstar) (by positivity) σ hσ t

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI

end Source2873

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseClippedUniform.lean; sha256: 81ed9ccd76253d82b0e6413a8a597780dd9eab0772e9d31fc98a056fb197729b -/
section Source2874
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseUniform HeckeInverseAmplification
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem source_support (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) :
    Function.support (inverseSourceSchwartz scaled reverse n U tstar r σ t : ℝ→ℂ) ⊆
      Set.Icc (1/4 : ℝ) (9/4) := by
  let W := inverseDetectorSchwartz reverse n (U^r/U^tstar) σ t
  have hw : Function.support (W : ℝ→ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) := by
    have he : (W : ℝ→ℂ) = twistProfile
        (baseProfile reverse n HeckeDetectorProfiles.cutoff
          HeckeDetectorDyadicProfiles.positiveAnnular (U^r/U^tstar)) σ t := by
      funext x
      exact inverseDetectorSchwartz_apply _ _ _ _ _ _
    rw [he]
    exact (twistProfile_support _ _ _).trans
      ((baseProfile_support _ _ _ _ _).trans HeckeDetectorDyadicProfiles.positiveAnnular_support)
  have ht : tsupport (W : ℝ→ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) :=
    closure_minimal hw isClosed_Icc
  cases scaled
  · exact hw
  · intro x hx
    by_contra hn
    have hz : W x = 0 := by
      by_contra h
      exact hn (hw h)
    have hd : deriv (W : ℝ→ℂ) x = 0 := by
      by_contra h
      exact hn (ht (support_deriv_subset h))
    apply hx
    change scaleCLM W x = 0
    rw [scaleCLM_apply]
    simp [scaleProfile, hz, hd]

theorem source_zero_of_ratio (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ)
    (h : 4 ≤ U^r/U^tstar) : inverseSourceSchwartz scaled reverse n U tstar r σ t = 0 :=
  inverseDetectorTest_zero_of_four_le scaled reverse n _ σ t h

theorem exists_reference_window :
    ∃w : 𝓢(ℝ,ℂ), HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ) ⊆ Set.Icc (1/18 : ℝ) (13/4) ∧
      ∀x∈Set.Icc (1/9 : ℝ) (9/4), w x = 1 := by
  obtain ⟨w,hc,hone,hs⟩ := InverseSecondChildWindows.positive_cutoff
    (1/9 : ℝ) (9/4) (by norm_num) (by norm_num)
  refine ⟨w,hc,?_,hone⟩
  convert hs using 1
  norm_num

def referenceWindow : 𝓢(ℝ,ℂ) := Classical.choose exists_reference_window

theorem referenceWindow_compact : HasCompactSupport (referenceWindow : ℝ→ℂ) :=
  (Classical.choose_spec exists_reference_window).1

theorem referenceWindow_support : tsupport (referenceWindow : ℝ→ℂ) ⊆
    Set.Icc (1/18 : ℝ) (13/4) :=
  (Classical.choose_spec exists_reference_window).2.1

theorem referenceWindow_one (x : ℝ) (hx : x∈Set.Icc (1/9 : ℝ) (9/4)) :
    referenceWindow x = 1 :=
  (Classical.choose_spec exists_reference_window).2.2 x hx

theorem referenceWindow_agrees (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c y : ℝ)
    (hc : 1≤c) (hcb : c≤9/4) (hy : 0<y) :
    referenceWindow y * inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) =
      inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) := by
  by_cases hz : inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) = 0
  · simp [hz]
  have hs := source_support scaled reverse n U tstar r σ t hz
  have hh : y∈Set.Icc (1/9 : ℝ) (9/4) := by
    constructor <;> nlinarith [hs.1,hs.2]
  rw [referenceWindow_one y hh,one_mul]

def logSource (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  CubicReflectionKernel.logPullbackCLM (1/4) (9/4)
    (inverseSourceSchwartz scaled reverse n U tstar r σ t)

theorem logSource_apply (scaled reverse : Bool) (n : ℕ) (U tstar r σ t x : ℝ) :
    logSource scaled reverse n U tstar r σ t x =
      inverseSourceSchwartz scaled reverse n U tstar r σ t (Real.exp x) :=
  CubicReflectionKernel.logPullbackCLM_eq_actual _ _ (by norm_num) _
    (source_support scaled reverse n U tstar r σ t) x

theorem logSource_eq_logSchwartz (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) :
    logSource scaled reverse n U tstar r σ t =
      CubicReflectionKernel.logSchwartz (inverseSourceSchwartz scaled reverse n U tstar r σ t)
        (1/4) (9/4) (by norm_num) (source_support scaled reverse n U tstar r σ t)
        ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤) := by
  ext x
  rw [logSource_apply,CubicReflectionKernel.logSchwartz_apply]

def familyDensity (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) : ℂ :=
  density (logSource scaled reverse n U tstar r σ t) (Real.log c) v

theorem familyDensity_formula (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) :
    familyDensity scaled reverse n U tstar r σ t c v =
      (𝓕 (logSource scaled reverse n U tstar r σ t)) v * logPhase v (Real.log c) := rfl

theorem familyDensity_norm (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) :
    ‖familyDensity scaled reverse n U tstar r σ t c v‖ =
      ‖(𝓕 (logSource scaled reverse n U tstar r σ t)) v‖ := density_norm _ _ _

theorem familyDensity_integrable (J : ℕ) (scaled reverse : Bool) (n : ℕ)
    (U tstar r σ t c : ℝ) :
    Integrable (fun v : ℝ => (1+‖v‖)^J * ‖familyDensity scaled reverse n U tstar r σ t c v‖) := by
  simp only [familyDensity_norm]
  exact AnalyticBridge.schwartz_fourier_one_plus_integrable _ _

theorem familyDensity_moment (J : ℕ) :
    ∃K : ℕ, ∃C : ℝ, 0<C ∧ ∀scaled reverse : Bool, ∀n : ℕ, n≤2 →
      ∀U : ℝ, 0<U → ∀tstar r : ℝ, ∀σ∈Set.Icc (0 : ℝ) 1, ∀t c : ℝ,
      (∫v : ℝ, (1+‖v‖)^J * ‖familyDensity scaled reverse n U tstar r σ t c v‖) ≤
        C*(1+‖t‖)^K := by
  let p := (volume : Measure ℝ).integrablePower
  let S : Finset (ℕ×ℕ) := Finset.Iic (p,J+p)
  obtain ⟨T,A,hA,hop⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (CubicReflectionKernel.logPullbackCLM (1/4) (9/4)) S
  obtain ⟨K,B,hB,hsource⟩ := inverseSourceSchwartz_uniform T
  let C := 1+(2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B)+coefficientMomentBound J (2*A*B))
  have hC : 0<C := by
    have h₀ := coefficientMomentBound_nonneg 0 (2*A*B) (by positivity)
    have hJ := coefficientMomentBound_nonneg J (2*A*B) (by positivity)
    dsimp [C]
    positivity
  refine ⟨K,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t c
  let W := inverseSourceSchwartz scaled reverse n U tstar r σ t
  let g := logSource scaled reverse n U tstar r σ t
  have hb : S.sup (schwartzSeminormFamily ℝ ℝ ℂ) g ≤ A*B*(1+‖t‖)^K := by
    exact (hop W).trans ((mul_le_mul_of_nonneg_left
      (hsource scaled reverse n hn U hU tstar r σ hσ t) hA.le).trans_eq (by ring))
  have hs (i : ℕ) (hi : i≤J+p) :
      (SchwartzMap.seminorm ℝ 0 i) g + (SchwartzMap.seminorm ℝ p i) g ≤
        2*A*B*(1+‖t‖)^K := by
    have h₀ : schwartzSeminormFamily ℝ ℝ ℂ (0,i) ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S,hi])
    have hp : schwartzSeminormFamily ℝ ℝ ℂ (p,i) ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S,hi])
    have h₁ := (Seminorm.le_def.mp h₀ g).trans hb
    have h₂ := (Seminorm.le_def.mp hp g).trans hb
    change (SchwartzMap.seminorm ℝ 0 i) g ≤ _ at h₁
    change (SchwartzMap.seminorm ℝ p i) g ≤ _ at h₂
    linarith
  have hmoment := uniform_fourier_one_plus_moment g J 1
    (2*A*B*(1+‖t‖)^K) (by norm_num) (by positivity)
    (by intro i hi; simpa only [one_mul] using hs i hi)
  simp only [one_mul] at hmoment
  simp only [familyDensity_norm]
  apply hmoment.trans
  have he : (2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B*(1+‖t‖)^K)+
      coefficientMomentBound J (2*A*B*(1+‖t‖)^K)) =
      ((2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B)+coefficientMomentBound J (2*A*B)))*(1+‖t‖)^K := by
    unfold coefficientMomentBound
    ring
  rw [he]
  dsimp [C]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

section Rows
variable {ι ρ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_family_mode_integrable
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m f k : O) (slots : Finset ρ)
    (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c θ X : ℝ) :
    Integrable (fun v : ℝ => familyDensity scaled reverse n U tstar r σ t c v *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
        (childLogTest referenceWindow (θ+v)) X) :=
  canonical_clipped_mode_integrable p hp hcop hg hpr pool Ψ m f k slots lists a
    (logSource scaled reverse n U tstar r σ t) referenceWindow c θ X

theorem canonical_clipped_family_fourier
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m f k : O) (slots : Finset ρ)
    (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c θ X : ℝ)
    (hc : 1≤c) (hcb : c≤9/4) (hX : 0<X) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (clippedTest (inverseSourceSchwartz scaled reverse n U tstar r σ t) c θ) X =
    ∫v : ℝ, familyDensity scaled reverse n U tstar r σ t c v *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
        (childLogTest referenceWindow (θ+v)) X := by
  simp only [familyDensity,logSource_eq_logSchwartz]
  exact canonical_clipped_fourier p hp hcop hg hpr pool Ψ m f k slots lists a
    (inverseSourceSchwartz scaled reverse n U tstar r σ t) (1/4) (9/4) (by norm_num)
    (source_support scaled reverse n U tstar r σ t)
    ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤)
    referenceWindow c θ X (zero_lt_one.trans_le hc) hX
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t c y hc hcb hy)
end Rows

theorem canonical_clipped_family_energy (J : ℕ) :
    ∃K : ℕ, ∃C : ℝ, 0<C ∧ ∀scaled reverse : Bool, ∀n : ℕ, n≤2 →
    ∀U : ℝ, 0<U → ∀tstar r : ℝ, ∀σ∈Set.Icc (0 : ℝ) 1, ∀t : ℝ,
    ∀{ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (slots : Finset ρ) (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O→ℝ) (_hD : ∀f∈labels,0≤D f)
    (c θ X Z F E : ℝ), 1≤c → c≤9/4 → 0<X → 0≤E →
    (∀s, normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest referenceWindow s) X Z F ≤ E*(1+‖s‖)^(2*J)) →
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest (inverseSourceSchwartz scaled reverse n U tstar r σ t) c θ) X Z F ≤
        C*E*(1+‖t‖)^(2*K)*(1+‖θ‖)^(2*J) := by
  obtain ⟨K,C,hC,hmass⟩ := familyDensity_moment J
  refine ⟨K,C^2,by positivity,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t ι ρ _ _ p hp _ hcop hg hpr
    pool Ψ m slots lists a labels rows D hD c θ X Z F E hc hcb hX hE he
  have hb := canonical_clipped_energy p hp hcop hg hpr pool Ψ m slots lists a
    labels rows D hD (inverseSourceSchwartz scaled reverse n U tstar r σ t)
    (1/4) (9/4) (by norm_num) (source_support scaled reverse n U tstar r σ t)
    ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤)
    referenceWindow c θ X Z F E J (zero_lt_one.trans_le hc) hX hE
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t c y hc hcb hy) he
  have hm := hmass scaled reverse n hn U hU tstar r σ hσ t c
  simp only [familyDensity_norm,logSource_eq_logSchwartz] at hm
  have hs := pow_le_pow_left₀
    (integral_nonneg (fun v : ℝ => by positivity)) hm 2
  apply hb.trans
  calc
    _ ≤ E*(1+‖θ‖)^(2*J)*(C*(1+‖t‖)^K)^2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by rw [mul_pow,←pow_mul]; ring_nf

theorem initial_raw_family_energy (J : ℕ) :
    ∃K : ℕ, ∃C : ℝ, 0<C ∧ ∀scaled reverse : Bool, ∀n : ℕ, n≤2 →
    ∀U : ℝ, 0<U → ∀tstar r : ℝ, ∀σ∈Set.Icc (0 : ℝ) 1, ∀t : ℝ,
    ∀{ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (slots : Finset ρ) (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O→ℝ) (_hD : ∀f∈labels,0≤D f)
    (Z N F E : ℝ) (z : JointLogSeparation.Frequency×(Fin 6→ℝ)) (h : ℝ), 1<Z → 0≤E →
    (h = -InverseInitialClippedColumns.leftHeight z ∨ h = InverseInitialClippedColumns.rightHeight z) →
    (∀s, normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest referenceWindow s) (Z^(max 0 N)) Z F ≤ E*(1+‖s‖)^(2*J)) →
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest (inverseSourceSchwartz scaled reverse n U tstar r σ t) h) (Z^N) Z F ≤
        C*E*(1+‖t‖)^(2*K)*
          (InverseMoment.tripleHeight (4*J) z.1 * InverseMoment.coordinateHeight (4*J) z.2) := by
  obtain ⟨K,C,hC,hbound⟩ := canonical_clipped_family_energy J
  refine ⟨K,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t ι ρ _ _ p hp _ hcop hg hpr
    pool Ψ m slots lists a labels rows D hD Z N F E z h hZ hE hh he
  let W := inverseSourceSchwartz scaled reverse n U tstar r σ t
  by_cases hne : (freshColumns p pool W (Z^N)).Nonempty
  · obtain ⟨hc,hcb⟩ := freshColumns_clipping_range p hp pool W (1/4) (9/4)
      Z N hZ (by norm_num) (source_support scaled reverse n U tstar r σ t) hne
    rw [InverseInitialEnergyCallerClipping.normalized_energy_clipping p hp hcop hg
      pool Ψ m slots lists a labels rows D W (by linarith) N h F]
    apply (hbound scaled reverse n hn U hU tstar r σ hσ t
      p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
      (Z^(max 0 N-N)) h (Z^(max 0 N)) Z F E hc hcb (by positivity) hE he).trans
    exact mul_le_mul_of_nonneg_left
      (InverseInitialEnergyCallerUniform.initial_height_bound J z h hh) (by positivity)
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
    change normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest W h) (Z^N) Z F ≤ _
    unfold normalizedColumnEnergy
    simp_rw [canonical_row_zero_of_freshColumns_empty p hp hcop hg pool Ψ m _ _
      slots lists a W (Z^N) h hz,mul_zero,norm_zero,zero_pow (by omega : (2 : ℕ)≠0),
      Finset.sum_const_zero,mul_zero,Finset.sum_const_zero]
    dsimp [InverseMoment.tripleHeight,InverseMoment.coordinateHeight]
    positivity

end SevenEighths.DetectorDictionaryInverseClippedUniform

end

end OAI

end Source2874

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawUniform.lean; sha256: db7fb9409d151965f45d81b2c45fc781d8a11bebee66442187df483fbc4cb1a4 -/
section Source2875
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace SevenEighths.DetectorDictionaryInverseRawUniform
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open DetectorDictionaryInverseUniform DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseRawFourier

private theorem rawMoment_mono (data : RowData) (W : ℝ→ℂ) (c κ A B : ℝ)
    (hAB : A≤B) (h : RawMoment data W c κ A) : RawMoment data W c κ B := by
  intro H D hH hD hHD rows hrows
  apply (h H D hH hD hHD rows hrows).trans
  gcongr

theorem raw_family_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀(data : RowData)(c κ A : ℝ),0≤A →
      (∀s,RawMoment data (childLogTest referenceWindow s) c κ (A*(1+‖s‖)^(2*J))) →
      ∀scaled reverse : Bool,∀n : ℕ,n≤2 → ∀U : ℝ,0<U →
      ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
      RawMoment data (inverseSourceSchwartz scaled reverse n U tstar r σ t)
        c κ (A*C*(1+‖t‖)^K) := by
  obtain ⟨K,B,hB,hmass⟩:=familyDensity_moment J
  refine ⟨2*K,B^2,sq_pos_of_pos hB,?_⟩
  intro data c κ A hA href scaled reverse n hn U hU tstar r σ hσ t
  let W:=inverseSourceSchwartz scaled reverse n U tstar r σ t
  let hs:=source_support scaled reverse n U tstar r σ t
  let g:=CubicReflectionKernel.logSchwartz W (1/4) (9/4) (by norm_num) hs (W.smooth ⊤)
  have hw : ∀x,referenceWindow x≠0 → x≤(13/4:ℝ) := by
    intro x hx
    exact (referenceWindow_support (subset_tsupport _ hx)).2
  have hagree : ∀y,0<y → referenceWindow y*W y=W y := by
    intro y hy
    simpa only [one_mul,W] using referenceWindow_agrees scaled reverse n U tstar r σ t 1 y
      (by norm_num) (by norm_num) hy
  have hh:=rawMoment_reference data W (1/4) (9/4) (by norm_num) hs (W.smooth ⊤)
    referenceWindow (13/4) c κ A J hA hw hagree href
  have hm : (∫v:ℝ,(1+‖v‖)^J*‖(𝓕 g) v‖)≤B*(1+‖t‖)^K := by
    have hb:=hmass scaled reverse n hn U hU tstar r σ hσ t 1
    simpa only [familyDensity_norm,logSource_eq_logSchwartz,g,W,hs] using hb
  apply rawMoment_mono data W c κ _ _ _ hh
  change A*(∫v:ℝ,(1+‖v‖)^J*‖(𝓕 g) v‖)^2≤_
  calc
    _≤A*(B*(1+‖t‖)^K)^2:=mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg (fun _=>by positivity)) hm 2) hA
    _= _:=by simp only [mul_pow,←pow_mul,Nat.mul_comm];ring

theorem raw_pair_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀(data : RowData)(c κ A : ℝ),0≤A →
      (∀s,RawMoment data (childLogTest referenceWindow s) c κ (A*(1+‖s‖)^(2*J))) →
      ∀reverse : Bool,∀n : ℕ,n≤2 → ∀U : ℝ,0<U →
      ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
      let W:=twistProfile
        (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t
      RawMoment data W c κ (A*C*(1+‖t‖)^K) ∧
      RawMoment data (scaleProfile W) c κ (A*C*(1+‖t‖)^K) := by
  obtain ⟨K,C,hC,hb⟩:=raw_family_uniform J
  refine ⟨K,C,hC,?_⟩
  intro data c κ A hA href reverse n hn U hU tstar r σ hσ t
  dsimp only
  have hefalse : (inverseSourceSchwartz false reverse n U tstar r σ t:ℝ→ℂ)=
      twistProfile (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
        (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t := by
    funext x
    simpa only [Bool.false_eq_true,ite_false] using inverseSourceSchwartz_apply false reverse n U tstar r σ t x
  have hetrue : (inverseSourceSchwartz true reverse n U tstar r σ t:ℝ→ℂ)=
      scaleProfile (twistProfile (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
        (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t) := by
    funext x
    simpa only [Bool.true_eq,ite_true] using inverseSourceSchwartz_apply true reverse n U tstar r σ t x
  exact ⟨hefalse ▸ hb data c κ A hA href false reverse n hn U hU tstar r σ hσ t,
    hetrue ▸ hb data c κ A hA href true reverse n hn U hU tstar r σ hσ t⟩

theorem raw_pair_height_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀(data : RowData)(c κ A : ℝ),0≤A →
      (∀s,RawMoment data (childLogTest referenceWindow s) c κ (A*(1+‖s‖)^(2*J))) →
      ∀reverse : Bool,∀n : ℕ,n≤2 → ∀U : ℝ,0<U →
      ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀height t : ℝ,0≤height →
      t∈Set.Icc (-height) height →
      let W:=twistProfile
        (logTest (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t
      RawMoment data W c κ (A*C*(1+height)^K) ∧
      RawMoment data (scaleProfile W) c κ (A*C*(1+height)^K) := by
  obtain ⟨K,C,hC,hb⟩:=raw_pair_uniform J
  refine ⟨K,C,hC,?_⟩
  intro data c κ A hA href reverse n hn U hU tstar r σ hσ height t hheight ht
  have hh:=hb data c κ A hA href reverse n hn U hU tstar r σ hσ t
  have hnorm : ‖t‖≤height := by simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using ht
  have hbound : A*C*(1+‖t‖)^K≤A*C*(1+height)^K := by gcongr
  exact ⟨rawMoment_mono data _ c κ _ _ hbound hh.1,
    rawMoment_mono data _ c κ _ _ hbound hh.2⟩

end SevenEighths.DetectorDictionaryInverseRawUniform

end

end OAI

end Source2875

/- Original source: OAI/NumberTheory/DirichletL/Detector/DetectorInverseRawField.lean; sha256: 405a368337f3dbf5ce14ce525de5c67a6949edffa9f193654c3832958c95e869 -/
section Source2876
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.ProbeDetectorInverseRawField
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open HeckeDetectorInverseFiberCount DetectorDictionaryInverseClippedUniform
open ProbeHighRowFamily ProbeFinalAssembly

private theorem raw_mono (data:RowData)(W:ℝ→ℂ)(c κ A B:ℝ)
    (hAB:A≤B)(h:RawMoment data W c κ A):RawMoment data W c κ B:=by
  intro H D hH hD hcap rows hrows
  apply (h H D hH hD hcap rows hrows).trans
  gcongr

theorem fixed_raw_profiles (c κ:ℝ)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C:ℝ,0<C ∧
      ∀reverse:Bool,∀n:ℕ,n≤2→∀U:ℝ,0<U→∀tstar r:ℝ,
      ∀s∈Set.Icc (0:ℝ) 1,∀height t:ℝ,0≤height→t∈Set.Icc (-height) height→
      let W:=twistProfile (logTest (orientedProfile reverse (inverseTest U tstar r)) n) s t;
      RawMoment data W c κ (C*(1+height)^J) ∧
      RawMoment data (scaleProfile W) c κ (C*(1+height)^J):=by
  obtain ⟨J,hreference⟩:=DetectorDictionaryInverseRawReference.raw_reference_moment
    referenceWindow (1/18) (13/4) c κ (by norm_num) (by norm_num)
    (fun x hx=>referenceWindow_support (subset_tsupport _ hx)) hc hκ
  obtain ⟨K,C,hC,hfamily⟩:=DetectorDictionaryInverseRawUniform.raw_pair_height_uniform J
  refine ⟨K,?_⟩
  intro data
  obtain ⟨A,hA,href⟩:=hreference data
  exact ⟨A*C,mul_pos hA hC,hfamily data c κ A hA.le href⟩

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

theorem source_batch_inverse_raw
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(εm:ℝ)(counts:CountParameters M H εm):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧
    ∀{Slot:Type*}{U a ε tstar T allowance:ℝ}{i:ℕ},0<U→
    ∀(B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S hS η→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height→∀n:ℕ,n≤2→∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J):=by
  obtain ⟨JB,hB⟩:=fixed_raw_profiles counts.cB counts.kB counts.cB_pos counts.kB_pos
  obtain ⟨JH,hHraw⟩:=fixed_raw_profiles counts.cH counts.kH counts.cH_pos counts.kH_pos
  refine ⟨JB+JH,?_⟩
  intro η
  let data:=sourceMomentData M H hH S hS η
  choose CB hCB hb using (fun label=>hB (data label))
  choose CH hCH hh using (fun label=>hHraw (data label))
  let C:ℝ:=1+(∑label,CB label)+(∑label,CH label)
  have hsumB:0≤∑label,CB label:=Finset.sum_nonneg (fun j _=>(hCB j).le)
  have hsumH:0≤∑label,CH label:=Finset.sum_nonneg (fun j _=>(hCH j).le)
  have hC:0<C:=by dsimp [C];linarith
  have hCBound (label):CB label≤C:=by
    have he:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hCB j).le) (Finset.mem_univ label)
    dsimp [C];linarith
  have hCHound (label):CH label≤C:=by
    have he:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hCH j).le) (Finset.mem_univ label)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro Slot U a ε tstar T allowance i hU B hdata bin label left right hne height hheight n hn s hs t ht F W
  have hd:F.rowData=data label:=by
    change B.data label=data label
    rw [hdata]
  have hbase:1≤1+height:=by linarith
  by_cases hbranch:2*a-1≤5/6
  · simp only [hbranch,ite_true]
    have hpair:=hb label F.reverse n hn U hU tstar F.r s hs height t hheight ht
    have hconstant:CB label*(1+height)^JB≤C*(1+height)^(JB+JH):=
      mul_le_mul (hCBound label) (pow_le_pow_right₀ hbase (Nat.le_add_right _ _))
        (by positivity) hC.le
    rw [hd]
    exact ⟨raw_mono _ _ _ _ _ _ hconstant hpair.1,raw_mono _ _ _ _ _ _ hconstant hpair.2⟩
  · simp only [hbranch,ite_false]
    have hpair:=hh label F.reverse n hn U hU tstar F.r s hs height t hheight ht
    have hconstant:CH label*(1+height)^JH≤C*(1+height)^(JB+JH):=
      mul_le_mul (hCHound label) (pow_le_pow_right₀ hbase (Nat.le_add_left _ _))
        (by positivity) hC.le
    rw [hd]
    exact ⟨raw_mono _ _ _ _ _ _ hconstant hpair.1,raw_mono _ _ _ _ _ _ hconstant hpair.2⟩

end SevenEighths.ProbeDetectorInverseRawField

end

end OAI

end Source2876

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialMarkedDictionary.lean; sha256: 76188e2eb11965ea223eb444d2f9264f058626ac05bbee1bac6c4d9900022cc8 -/
section Source2877
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialMarkedDictionary
open HeckeFamily HeckeDyadic InverseInitialRawDictionary InverseInitialConjugateEnergy
open InverseInitialPoissonBridge UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem indexed_mark_initial {ι : Type*} (T : Finset ι) (P : ι→Ideal O) (A : ι→ℂ)
    (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ→ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hc : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑i∈T,A i*idealCoeff χ (P i))=
      ∑i∈T,A i*originalTotalPolynomial S (P i) η (fun _=>1)
        (twistedProfile W σ freq) Z r z u := by
  rw [inverse_eq_initial_source η χ u hrow W Z r σ freq hZ S hc]
  have hn : ((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ)=((Z^(-(r+z)/2):ℝ):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.rpow_add hZ]
    congr 2
    ring
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro I hI
  rw [hrow]
  simp only [heckeIdealCharacter_apply]
  calc
    _ = (((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ))*
      (A i*((moebius I:ℂ)*(η I*CanonicalRowCompletion.idealRowHom u I)*
      (η (P i)*CanonicalRowCompletion.idealRowHom u (P i))*
      twistedProfile W σ freq ((I.absNorm:ℝ)/Z^r))) := by ring
    _ = _ := by rw [hn];ring

theorem indexed_conjugate_mark_norm {ι : Type*} (T : Finset ι) (P : ι→Ideal O) (A : ι→ℂ)
    (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ→ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hc : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S)
    (hη : ∀i∈T,A i≠0 → η (P i)≠0) :
    ‖polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑i∈T,A i*star (CanonicalRowCompletion.idealRowHom u (P i)))‖=
      ‖∑i∈T,(star (A i)/η (P i))*originalTotalPolynomial S (P i) η (fun _=>1)
        (twistedProfile W σ freq) Z r z u‖ := by
  have hm : (∑i∈T,(star (A i)/η (P i))*idealCoeff χ (P i))=
      star (∑i∈T,A i*star (CanonicalRowCompletion.idealRowHom u (P i))) := by
    simp only [star_sum,star_mul,star_star]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : A i=0
    · simp [ha]
    · rw [hrow]
      field_simp [hη i hi ha]
  rw [←indexed_mark_initial T P (fun i=>star (A i)/η (P i)) η χ u hrow W Z r z σ freq hZ S hc,hm]
  simp only [norm_mul,norm_star]

theorem conjugate_mark_product {ι : Type*} [Fintype ι]
    (T : ι→Finset (Ideal O)) (A : ι→Ideal O→ℂ) (u : O) :
    (∏i,∑P∈T i,A i P*star (CanonicalRowCompletion.idealRowHom u P))=
      ∑p∈Fintype.piFinset T,(∏i,A i (p i))*
        star (CanonicalRowCompletion.idealRowHom u (∏i,p i)) := by
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.prod_mul_distrib,map_prod,star_prod]

end SevenEighths.InverseInitialMarkedDictionary

end

end OAI

end Source2877

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialPhysicalSlots.lean; sha256: 8649cca47ab87613b3251c38f8bbc141cd2caa121bce68ed8d88f7136edb4e49 -/
section Source2878
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialPhysicalSlots
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialMarkedDictionary
open InverseInitialConjugateEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def livePrimes (V : ℝ→ℂ) (b D : ℝ) : Finset (Ideal O) :=
  ((HeckePrimeAnnular.annulusSet b D).filter
    (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H)).filter
      (fun P=>V ((P.absNorm:ℝ)/D)≠0)

omit [NeZero M] in
theorem livePrime_data (V : ℝ→ℂ) (a b D : ℝ) (hD : 0<D)
    (hV : ∀x,V x≠0 → x∈Set.Icc a b) (P : Ideal O) (hp : P∈livePrimes M H V b D) :
    Prime P ∧ P∈RayQuotient.identityClass M H ∧ a*D≤(P.absNorm:ℝ) ∧ (P.absNorm:ℝ)≤b*D := by
  obtain ⟨hp,hv⟩ := Finset.mem_filter.mp hp
  obtain ⟨_,hp,hr⟩ := Finset.mem_filter.mp hp
  exact ⟨hp,hr,(le_div_iff₀ hD).mp (hV _ hv).1,(div_le_iff₀ hD).mp (hV _ hv).2⟩

omit [NeZero M] in
theorem amplitude_eq_live (u : O) (V : ℝ→ℂ) (b Z ell : ℝ) (ζ : ℂ) (hZ : 0<Z) :
    HeckePrimeRow.canonicalPrimeAmplitude M H u V b (Z^ell) ζ=
      ((Z^(-ell/2):ℝ):ℂ)*∑P∈livePrimes M H V b (Z^ell),
        primeProfile V (Z^ell) ζ P*star (CanonicalRowCompletion.idealRowHom u P) := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude
  rw [normalization_eq Z ell hZ]
  congr 1
  rw [livePrimes]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hP
  split_ifs with hv
  · change star (CanonicalRowCompletion.idealRowHom u P)*V _*_ =
      (V _*_)*star (CanonicalRowCompletion.idealRowHom u P)
    ring
  · simp only [not_not] at hv
    simp [hv]

theorem slot_normalization {ι : Type*} [Fintype ι] (Z : ℝ) (hZ : 0<Z) (ell : ι→ℝ) :
    (∏i,((Z^(-ell i/2):ℝ):ℂ))=((Z^(-(∑i,ell i)/2):ℝ):ℂ) := by
  rw [←Complex.ofReal_prod,←Real.rpow_sum_of_pos hZ]
  congr 2
  simp only [neg_div,Finset.sum_div,Finset.sum_neg_distrib]

omit [NeZero M] in
theorem amplitude_product_eq_tuples {ι : Type*} [Fintype ι] (u : O)
    (V : ι→ℝ→ℂ) (b ell : ι→ℝ) (ζ : ι→ℂ) (Z : ℝ) (hZ : 0<Z) :
    (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u (V i) (b i) (Z^(ell i)) (ζ i))=
      ((Z^(-(∑i,ell i)/2):ℝ):ℂ)*
        ∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
        (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))*
          star (CanonicalRowCompletion.idealRowHom u (∏i,p i)) := by
  simp_rw [amplitude_eq_live M H _ _ _ _ _ _ hZ]
  rw [Finset.prod_mul_distrib,slot_normalization Z hZ,conjugate_mark_product]

omit [NeZero M] in
theorem physical_slots_norm_initial {ι : Type*} [Fintype ι]
    (data : RowData) (u : NonzeroElement) (W : ℝ→ℂ) (V : ι→ℝ→ℂ)
    (Z r σ freq bW : ℝ) (a b ell : ι→ℝ) (ζ : ι→ℂ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤bW) (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hlarge : ∀i,((baseCharacter data).modulus.absNorm:ℝ)<a i*Z^(ell i)) :
    ‖polynomial (data.character u) true W (Z^r) σ freq*
      (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (Z^(ell i)) (ζ i))‖=
    ‖∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
      (star (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))/
        fixedBase data.η data.m data.f (∏i,p i))*
      originalTotalPolynomial
        ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
        (∏i,p i) (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile W σ freq) Z r (∑i,ell i) u.val‖ := by
  let T := fun i=>livePrimes M H (V i) (b i) (Z^(ell i))
  let A := fun p:ι→Ideal O=>∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i)
  have hn (p : ι→Ideal O) (hp : p∈Fintype.piFinset T) (_ha : A p≠0) :
      fixedBase data.η data.m data.f (∏i,p i)≠0 := by
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hpi := Fintype.mem_piFinset.mp hp i
    have hd := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
      (Real.rpow_pos_of_pos hZ _) (hV i) (p i) hpi
    exact base_nonzero_prime data (p i) hd.1 ((hlarge i).trans_le hd.2.2.1)
  have he := indexed_conjugate_mark_norm (Fintype.piFinset T) (fun p=>∏i,p i) A
    (fixedBase data.η data.m data.f) (data.character u) u.val
    (fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u))
    W Z r (∑i,ell i) σ freq hZ (ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊)
    (finite_source_cover W (Z^r) bW (Real.rpow_pos_of_pos hZ _) hW) hn
  rw [amplitude_product_eq_tuples M H _ _ _ _ _ _ hZ,←mul_assoc]
  change ‖polynomial (data.character u) true W (Z^r) σ freq*↑(Z^(-(∑i,ell i)/2))*
    (∑p∈Fintype.piFinset T,A p*star (CanonicalRowCompletion.idealRowHom u (∏i,p i)))‖=_
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [originalTotal_supported_source _ _ _
    (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd)]

omit [NeZero M] in
theorem live_tuple_injective {ι : Type*} [Fintype ι]
    (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) : Function.Injective p := by
  intro i j he
  by_contra hij
  have hi := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hj := livePrime_data M H (V j) (a j) (b j) (Z^(ell j))
    (Real.rpow_pos_of_pos hZ _) (hV j) (p j) (Fintype.mem_piFinset.mp hp j)
  rw [he] at hi
  rcases hsep i j hij with h|h <;> linarith [hi.2.2.1,hi.2.2.2,hj.2.2.1,hj.2.2.2]

omit [NeZero M] in
theorem live_tuple_admissible {ι : Type*} [Fintype ι]
    (data : RowData) (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hlarge : ∀i,((baseCharacter data).modulus.absNorm:ℝ)<a i*Z^(ell i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) :
    CanonicalQuadraticSieve.Admissible (∏i,p i) := by
  have hd i := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hs (i : ι) : CanonicalQuadraticSieve.Supported (p i) := by
    by_contra hn
    exact base_nonzero_prime data (p i) (hd i).1 ((hlarge i).trans_le (hd i).2.2.1)
      (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd (p i) hn)
  have hi := live_tuple_injective M H V a b ell Z hZ hV hsep p hp
  have hsprod : CanonicalQuadraticSieve.Supported (∏i,p i) := by
    have hh (S : Finset ι) : CanonicalQuadraticSieve.Supported (∏i∈S,p i) := by
      induction S using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
      | @insert i S hi ih =>
        rw [Finset.prod_insert hi]
        exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr ⟨hs i,ih⟩
    exact hh Finset.univ
  refine ⟨hsprod.1,?_,?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      let : (p i).IsMaximal := (Ideal.isPrime_of_prime (hd i).1).isMaximal (hd i).1.ne_zero
      let : (p j).IsMaximal := (Ideal.isPrime_of_prime (hd j).1).isMaximal (hd j).1.ne_zero
      exact (Ideal.isCoprime_of_isMaximal (hi.ne hij)).isRelPrime
    · intro i _
      exact (hd i).1.squarefree
  · intro P hP
    exact hsprod.2 P hP

end SevenEighths.InverseInitialPhysicalSlots

end

end OAI

end Source2878

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseRawFiberSource.lean; sha256: ad5c8655f2aba6e08e20b002f3faf002d3c87de4d4b4765ec42d4d8d676467b7 -/
section Source2879
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.DetectorDictionaryInverseRawFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy
open HeckeDetectorPhysicalSelection
local notation "O"=>HeckeFamily.O

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem fiber_physical_norm_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s))
    (u : FreeRow) (hu : u∈F.rows) :
    ‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖=
      ‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖ := by
  have hn:=norm_of_oriented_coefficients (F.family u F.label)
    (F.rowData.character ⟨u.val,u.property.1⟩) F.reverse (F.row_coeff u hu)
    true W (U^F.r) σ t (Real.rpow_pos_of_pos hU _)
  have hp : F.physicalProduct selected u=
      ∏s:selected,HeckePrimeRow.canonicalPrimeAmplitude M H u.val
        (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s) := by
    simp only [Fiber.physicalProduct,physical]
    exact (Finset.prod_coe_sort selected _).symm
  rw [norm_mul,hn,←norm_mul,hp]
  have hh:=physical_slots_norm_initial M H F.rowData ⟨u.val,u.property.1⟩
    (orientedProfile F.reverse W) (fun s:selected=>F.profile s)
    U F.r σ (orientedFrequency F.reverse t) bW
    (fun s:selected=>lower s) (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
    (fun s:selected=>F.external s) hU
    (by intro x hx;apply hW x;intro hz;exact hx (by cases F.reverse <;> simp [orientedProfile,hz]))
    (fun s=>hV s s.property) (fun s=>hlarge s s.property)
  convert hh using 1 ; congr 2
  ext p
  simp only [Fintype.mem_piFinset]

theorem fiber_physical_energy_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [fiber_physical_norm_initial F selected W σ t bW lower hU hW hV hlarge u hu]

theorem fiber_inverse_log_upper
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (n : ℕ) :
    ∀x,((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) x≠0 → x≤9/4 := by
  induction n with
  | zero =>
    intro x hx
    have hv : HeckeDetectorDyadicProfiles.positiveAnnular x≠0 := by
      intro hz
      exact hx (by simp [Fiber.inverseProfile,HeckeDetectorInverseFiberCount.inverseTest,
        HeckeDetectorDyadicBridge.inverseProfile,hz])
    exact (HeckeDetectorDyadicProfiles.positiveAnnular_support hv).2
  | succ n ih =>
    intro x hx
    rw [Function.iterate_succ_apply'] at hx
    exact ih x (HeckeDetectorRowwisePolynomial.logProfile_support _ hx)

theorem fiber_inverse_energy_initial
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (n : ℕ) (σ t : ℝ) (lower : Slot→ℝ)
    (hU : 0<U)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) (U^F.r) σ t*F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖∑p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
          fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*(9/4)⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u.val‖^2 := by
  exact fiber_physical_energy_initial F selected
    ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) σ t (9/4) lower
    hU (fiber_inverse_log_upper F n) hV hlarge

end SevenEighths.DetectorDictionaryInverseRawFiberSource

end

end OAI

end Source2879
