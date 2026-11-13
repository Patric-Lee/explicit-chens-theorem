import OpenAIGrouped.Unit040
import OpenAIGrouped.Unit039
import OpenAIGrouped.Unit035
import OpenAIGrouped.Unit038

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalExponent.lean; sha256: f1256a54a08c1c2d0f090aad85d00481a703bcf29dc7de8259bde403ebe49faf -/
section Source1640
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_energy_exponent
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧
    ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (e : A→Fin 3)
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))
      InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
        (normWidth Z (frozenExtracted G j e 2)) za v ell (ramifiedWidth Z i.1)
        (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+v+ell+za)+η/2+O₀/2≤F₀-cstar/4 := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := original_surviving_terminal_saving s hc₀ kK kP η hkK hkP hηpos
  refine ⟨Z₀,hZ₀,?_⟩
  intro J I F B R Q₀ hJ hI hF hB hR hpower hmask A e column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret hsurv
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hs := hsave J I F B R Q₀ hJ hI hF hB hR hpower hmask A e column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hret hsurv
  have hb := retained_extracted_log_budget (familyRawScale G s X QK QP) Z δ Lscale Lrow Lslot η
    (kK*QK) (kP*QP) (familyRawScale_pos G s hc₀ X QK QP hX hQK hQP)
    (lt_of_lt_of_le hZ₀ hZ) (mul_pos hkK hQK) (mul_pos hkP hQP) hscap hconst hrowcap hslotcap i hret
    (frozenExtracted G j e 1) (frozenExtracted G j e 2)
    (frozenExtracted_ne_zero G j e 1) (frozenExtracted_ne_zero G j e 2)
  rw [←heH,←heza] at hb
  have he := mul_le_mul_of_nonneg_left hb hε
  dsimp only [G,j] at hs hb he
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1640

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalBranchSum.lean; sha256: eccf5f6dd531ec629b11c7002d300b09468ab439399eae844cce92d6afd4adc7 -/
section Source1641
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_energy_sum
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (ρ : ℝ) (hρ : 0<ρ) (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ C : ℝ, 1<Z₀ ∧ 0<C ∧
    ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      ((branches.card:ℝ)*∑ e∈branches,
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))≤
        C*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := original_surviving_energy_exponent s hc₀ kK kP η hkK hkP hηpos
  obtain ⟨C,hC,hcount⟩ := surviving_branch_count_small_power ρ hρ
  refine ⟨Z₀,C,hZ₀,hC,?_⟩
  intro J I F B R Q₀ hJ hI hF hB hR hpower hmask A column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hcbr := hcount G ((poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise
    (poolPrimeFamily_pairwise J (B*F*R) Q₀) A) j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hb (e : A→Fin 3) (he : e∈branches) := hsave J I F B R Q₀ hJ hI hF hB hR hpower hmask A e column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε hrowcap hslotcap hconst hbudget hscap hret he
  calc
    _ ≤ (branches.card:ℝ)*∑ _e∈branches,Z^(F₀-cstar/4-O₀/2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he
      apply Real.rpow_le_rpow_of_exponent_le hz'.le
      have hh := hb e he
      dsimp only at hh
      linarith
    _ = ((branches.card:ℝ)^2)*Z^(F₀-cstar/4-O₀/2) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcbr (Real.rpow_nonneg (lt_trans zero_lt_one hz').le _)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1641

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalSector.lean; sha256: 2658bf9a8caf3ad083cb84b799b1dd5906df5faad6b9fff52481975c75fd8f29 -/
section Source1642
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_literal_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (u : Eisˣ) (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalDyadicRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨degree,C₀,Cs,Zs,hC₀,hCs,hZs,henergy⟩ := sector_normalized_literal_energy
    (N:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ η hηpos
  obtain ⟨Zb,Cb,hZb,hCb,hbranch⟩ := original_surviving_energy_sum s hc₀ ρ hρ 1 (1/2) η
    (by norm_num) (by norm_num) hηpos
  let Kc := (Real.exp (Real.log 2/2+Real.log 2))^2*(6*Cs)
  have hKc : 0<Kc := by dsimp [Kc];positivity
  refine ⟨degree*2,Kc*Cb*C₀^2+1,max Zs Zb,by positivity,lt_of_lt_of_le hZs (le_max_left _ _),?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar u θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZs ((le_max_left _ _).trans hZ))
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A
  have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
  have hs := henergy Z ((le_max_left _ _).trans hZ) G j hNlevel hbase hac hpair hGN hGchar hj
    rows Pset S hrows E hrowcop hprod hScop hSN hSchar u i X θ QK QP r aw hX hqk hqp hKr hPr hr haw
  have hb := hbranch J I F B R Q₀ hJ hI hF hB hR hpower hmask A (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    ((le_max_right _ _).trans hZ) hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    (by simpa only [one_mul] using heH) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using heza)
    heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε.le
    (by simpa only [one_mul] using hrowcap) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hslotcap)
    hconst hbudget hscap hret
  dsimp only at hs hb
  rw [←heH,←heza,←heN] at hs
  simp_rw [←Finset.mul_sum] at hs
  apply hs.trans
  calc
    _ = Kc*((survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)).card*
      ∑ e∈survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1),
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by dsimp [Kc,G,j];ring
    _ ≤ Kc*(Cb*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2))*(C₀*(1+‖θ‖)^degree)^2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKc.le) (sq_nonneg _)
    _ = (Kc*Cb*C₀^2)*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by rw [mul_pow,←pow_mul];ring
    _ ≤ _ := by gcongr;linarith
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1642

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalRetained.lean; sha256: a3a5739231322f96c9a17077a4aed0559fcff57c7c679569c2c5d944d1793c0e -/
section Source1643
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_retained_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*((retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)).card:ℝ)^2*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_sector_literal_energy
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
  refine ⟨degree,36*C,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let Dset := retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)
  let src := fun (ui : Eisˣ×(ℕ×ℕ×ℕ)) (K : rows) =>
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ ui.1 ui.2 W θ X r aw
  have hb (ui : Eisˣ×(ℕ×ℕ×ℕ)) (hui : ui∈(Finset.univ:Finset Eisˣ)×ˢDset) :=
    henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
      Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot ui.2
      hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
      heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap
      (Finset.mem_product.mp hui).2 rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
      ui.1 θ r aw hqk hqp hKr hPr hr haw
  have hh := weighted_finite_row_energy_uniform ((Finset.univ:Finset Eisˣ)×ˢDset) (Finset.univ:Finset rows)
    (fun _ => (1:ℂ)) src _ hb
  have hcard : Fintype.card Eisˣ=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  simp only [src,one_mul,norm_one,Finset.sum_const,nsmul_eq_mul,mul_one,
    Finset.card_product,Finset.card_univ,hcard,Finset.sum_product,tsum_fintype] at hh ⊢
  apply hh.trans_eq
  push_cast
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1643

/- Original source: OAI/NumberTheory/DirichletL/Reflection/RetainedBudget.lean; sha256: 5e9f966619e8254ce71eafe0b04eb49164ee00d3df8afcad286f1f25887b4bc5 -/
section Source1644
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_retained_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (_hLpool : 0≤Lpool) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_sector_retained_energy
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
  obtain ⟨Cd,hCd,hcount⟩ := retained_count_budget κ δ Lscale hκ hδL
  refine ⟨degree,C*Cd,Z₀,mul_pos hC hCd,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have hs := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have hd := hcount Z (familyRawScale G s X QK QP) hz'.le hscap
  have hp : (Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ≤Z^(Lpool*ρ) := by
    rw [Real.rpow_mul hzpos.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hpool hρ.le
  apply hs.trans
  calc
    _ ≤ C*(Cd*Z^κ)*(1+‖θ‖)^degree*Z^(Lpool*ρ)*Z^(F₀-cstar/4-O₀/2) := by gcongr
    _ = (C*Cd)*(1+‖θ‖)^degree*Z^(κ+Lpool*ρ+(F₀-cstar/4-O₀/2)) := by
      rw [Real.rpow_add hzpos,Real.rpow_add hzpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz'.le (by nlinarith only [hsmall])) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1644

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalFull.lean; sha256: 452b30d5c3aeae1f1caecd5bcbe455ff3cff0ec17372db01d1f8aa6d78474618 -/
section Source1645
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_full_energy
    (Adecay : ℕ) (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool) :
    ∃ (degree degreeTail : ℕ) (C Ctail Z₀ : ℝ), 0<C ∧ 0<Ctail ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2)+
          2*rows.card*(Pset.card*Ctail*(1+‖θ‖)^degreeTail*
            ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*
            (familyRawScale G s X QK QP^2)⁻¹)^2 := by
  obtain ⟨degree,Cm,Z₀,hCm,hZ₀,henergy⟩ := original_sector_retained_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  obtain ⟨degreeTail,Ct,hCt,htail⟩ := original_family_whole_tail
    (N:=Nlevel) (a:=a) (c:=c₀) (mode:=mode) lo hi hlo Adecay W hWs hW
  let Cshape := ‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖
  let Ctail := 6*Cshape*Ct+1
  have hshape : 0≤Cshape := by dsimp [Cshape];positivity
  have hCtail : 0<Ctail := by dsimp [Ctail];positivity
  refine ⟨degree,degreeTail,2*Cshape^2*Cm+1,Ctail,Z₀,by positivity,hCtail,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let Φ := fixedRadialCoefficientScalar*s.stratumShapeFactor (c₀*primaryGenerator (∏ b,G.ideal b))
  let g := fun K : rows => ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ u i W θ X rr aa
  let f := fun K : rows => literalWholeRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ W θ X r aw
  let Et := (Pset.card:ℝ)*Ctail*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
    (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hEt : 0≤Et := by dsimp [Et];positivity
  have hΦ : ‖Φ‖=Cshape := by
    dsimp only [Φ,Cshape]
    rw [norm_mul,stratumShapeFactor_frozen_norm]
  have hmain := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap hpool hsmall
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ rr aa hqk hqp hKr hPr
    (fun K hK => by simpa only [rr,row_shape_weight_norm r K (hrows K hK)] using hr K hK)
    (fun P hP => by simpa only [aa,slot_shape_weight_norm aw P (hPr P hP).1] using haw P hP)
  have hrem (K : rows) : ‖f K-Φ*g K‖≤Et := by
    have hodd : ∀ P∈Pset,∀ b,ringChar (Eis⧸(G.reflected K.val (hrows K.val K.property) (S P)).ideal b)≠2 := by
      intro P hP b
      rcases b with b | b | b
      · exact hGchar b
      · exact ((hrows K.val K.property).2.2 b.val (Multiset.mem_toFinset.mp b.property)).2
      · exact hSchar P hP (Sum.inr b)
    have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
    have hh := htail G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ hNlevel hbase
      hodd hj hprod (fun P hP => (hPr P hP).1) θ X (Z^δ) QK QP r aw hX
      (Real.rpow_pos_of_pos hzpos _) hQK hQP (hKr K.val K.property).2
      (fun P hP => (hPr P hP).2.2) (hr K.val K.property) haw
    apply hh.trans
    change _ ≤ Et
    dsimp only [Et,Ctail,Cshape]
    have he : (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Pset.card*
        (Ct*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)=
      Pset.card*(6*(‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Ct)*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹ := by ring
    rw [he]
    gcongr
    linarith only
  have hh := row_energy_le_retained (Finset.univ:Finset rows) f (fun K => Φ*g K) Et hEt (fun K _ => hrem K)
  simp only [norm_mul,mul_pow,hΦ,←Finset.mul_sum,Finset.card_univ,Fintype.card_coe] at hh
  apply hh.trans
  calc
    _ ≤ 2*(Cshape^2*(Cm*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2)))+2*rows.card*Et^2 := by gcongr
    _ ≤ _ := by
      dsimp only [Et]
      have hp : 0≤(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by positivity
      nlinarith only [hp]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1645

/- Original source: OAI/NumberTheory/DirichletL/Reflection/FullBudget.lean; sha256: 66de89623690d1b141091c4a6a627ba8e50ef1066917e32d1d4aa4000dcbfe70 -/
section Source1646
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_full_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤F₀-3*cstar/16-O₀/2 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨Adecay,htail⟩ := actual_finite_source_tail_budget s Lcap δ saving hδ
  obtain ⟨degree,degreeTail,Cm,Ct,Z₀,hCm,hCt,hZ₀,henergy⟩ := original_sector_full_energy
    (Nlevel:=Nlevel) Adecay ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  let cusp := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c₀}):ℝ)^2
  let deg := max degree (degreeTail*2)
  refine ⟨deg,Cm+2*Ct^2*cusp^4+1,max Z₀ 128,by positivity,
    lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ ((le_max_left _ _).trans hZ)
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have h128 : 128≤Z := (le_max_right _ _).trans hZ
  have hs := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    ((le_max_left _ _).trans hZ) hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap hpool hsmall
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have ht := htail G rows Pset Z X QK QP h128 hX hqk (by linarith only [hqp])
    (fun K hK => ⟨(hrows K hK).1,(hKr K hK).2⟩)
    (fun P hP => ⟨(hPr P hP).1.1.ne_zero,(hPr P hP).2.2⟩) hFcap hKcap hPcap hXi
  have hheight : 1≤1+‖θ‖ := by linarith only [norm_nonneg θ]
  have hdm : (1+‖θ‖)^degree≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_left _ _)
  have hdt : (1+‖θ‖)^(degreeTail*2)≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_right _ _)
  have he := Real.rpow_le_rpow_of_exponent_le hz'.le hexp
  apply hs.trans
  have htailbound : 2*rows.card*(Pset.card*Ct*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2≤
      (2*Ct^2*cusp^4)*(1+‖θ‖)^deg*Z^(F₀-3*cstar/16-O₀/2) := by
    calc
      _ = (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*
          (rows.card*(Pset.card*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
            (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2) := by rw [pow_mul];ring
      _ ≤ (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*(cusp^4*Z^(-saving)) := by
        exact mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ (2*Ct^2*(1+‖θ‖)^deg)*(cusp^4*Z^(F₀-3*cstar/16-O₀/2)) := by gcongr
      _ = _ := by ring
  have hmain : Cm*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2)≤
      Cm*(1+‖θ‖)^deg*Z^(F₀-3*cstar/16-O₀/2) := by gcongr
  apply (add_le_add hmain htailbound).trans
  have hp : 0≤(1+‖θ‖)^deg*Z^(F₀-3*cstar/16-O₀/2) := by positivity
  nlinarith only [hp]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1646

/- Original source: OAI/NumberTheory/DirichletL/Reflection/GlobalBudget.lean; sha256: cb1218539a8c5309b7b0ec14946749dc3acfa71d0ffb942ac8a131fcde125525 -/
section Source1647
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_global_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤F₀-3*cstar/16-O₀/2 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (D K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_sector_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  let q := (Fintype.card (Eis⧸Ideal.span {Nlevel^2}):ℝ)
  have hq : 0≤q := Nat.cast_nonneg _
  refine ⟨degree,q^3*C+1,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool hsmall rows Pset S hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A
  obtain ⟨D,hD⟩ := exists_global_sector_completion G rows Pset S hrows s hc₀ hNlevel hbase hac hpair hGN
    hrowcop hprod hScop (fun P hP b => hSN P hP (Sum.inr b))
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hs := literal_global_sector_energy G rows Pset S hrows j D s hc₀ W θ X r aw
    (C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2)) (by
      intro r₀ p₀
      obtain ⟨E,hE⟩ := hD r₀ p₀
      refine ⟨E,hE,?_⟩
      exact henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
        Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
        hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
        heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
        hFcap hscap hpool hsmall (fullRaySector Nlevel rows r₀) (fullRaySector Nlevel Pset p₀) S
        (fun K hK => hrows K (Finset.mem_filter.mp hK).1) E hGN hGchar
        (fun K hK => hrowcop K (Finset.mem_filter.mp hK).1)
        (fun P hP => hprod P (Finset.mem_filter.mp hP).1)
        (fun P hP => hScop P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSN P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSchar P (Finset.mem_filter.mp hP).1)
        θ r aw hqk hqp
        (fun K hK => hKr K (Finset.mem_filter.mp hK).1)
        (fun P hP => hPr P (Finset.mem_filter.mp hP).1)
        (fun K hK => hr K (Finset.mem_filter.mp hK).1)
        (fun P hP => haw P (Finset.mem_filter.mp hP).1))
  apply hs.trans
  change q^3*(C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2))≤_
  have hp : 0≤(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by positivity
  nlinarith only [hp]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1647

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MemberBudget.lean; sha256: 9bc1ec8a7fa4a9f4856e9c1acf7a168139bb64d653e46986c6205d9a41bd3011 -/
section Source1648
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_member_tuple_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤F₀-3*cstar/16-O₀/2 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_global_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool hsmall rows tuples hne hmax hgood hinj
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  obtain ⟨D,hD⟩ := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool hsmall rows (tuples.image slotTupleProduct) (tuplePrimeFamily tuples hne hmax hgood)
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have he := hD θ r (slotProductCoefficient tuples aw) hqk hqp hKr hPr hr
    (fun P hP => slotProductCoefficient_norm tuples hinj aw haw P hP)
  convert he using 1
  apply Finset.sum_congr rfl
  intro K hK
  congr 2
  exact (literalWholeRow_eq_member_tuples tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw).symm
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1648

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MemberGeometry.lean; sha256: 7fe6a5601512da70806482bcbbd51d4db834027f22e6645af40f391ffdf8a6f8 -/
section Source1649
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem original_member_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i)) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤F₀-3*cstar/16-O₀/2 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  have hb (i : γ) := original_member_tuple_full_budget (Nlevel:=Nlevel)
    ε hε lo hi hlo W hWs hW (s i) (hc₀ i) (hNlevel i) (hbase i) (hac i)
    ρ hρ η hηpos κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  choose degree C Z₀ hC hZ₀ henergy using hb
  let degreeAll := ∑ i,degree i
  let CAll := (∑ i,C i)+1
  let ZAll := (∑ i,|Z₀ i|)+2
  have hn (i : γ) : degree i≤degreeAll := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hc (i : γ) : C i≤CAll := by
    have hh : C i≤∑ j,C j := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
    dsimp only [CAll]
    linarith
  have hz (i : γ) : Z₀ i≤ZAll := by
    have hh : |Z₀ i|≤∑ j,|Z₀ j| := Finset.single_le_sum (fun j _ => abs_nonneg (Z₀ j)) (Finset.mem_univ i)
    have hh' := le_abs_self (Z₀ i)
    dsimp only [ZAll]
    linarith
  have hCA : 0<CAll := by
    have hh : 0≤∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    dsimp only [CAll]
    linarith
  have hZA : 1<ZAll := by
    have hh : 0≤∑ i,|Z₀ i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    dsimp only [ZAll]
    linarith
  refine ⟨degreeAll,CAll,ZAll,hCA,hZA,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hzwidth hzcap hcstar hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool hsmall rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  obtain ⟨D,hD⟩ := henergy i J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    ((hz i).trans hZ) hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hzwidth hzcap hcstar hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool hsmall rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  apply (hD θ r aw hqk hqp hKr hPr hr haw).trans
  have hZpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZA hZ)
  have hheight : 1≤1+‖θ‖ := by linarith [norm_nonneg θ]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
  exact mul_le_mul (hc i) (pow_le_pow_right₀ hheight (hn i)) (by positivity) hCA.le
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1649

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SourceScaleCaps.lean; sha256: 970b166597c9d19cdb8029e4f598bbc070f1d8c8c6a9e550810173d75c51478c -/
section Source1650
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma familyRawScale_inverse {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (X QK QP : ℝ) :
    (familyRawScale F s X QK QP)⁻¹=
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)*
        (Ideal.absNorm (∏ i,F.ideal i):ℝ)^2*QK^2*QP^2*X⁻¹ := by
  unfold familyRawScale actualKernelCoefficient fixedKernelCoefficient
  simp only [ramifiedScale,pow_zero,map_mul,map_one,Nat.cast_mul,Nat.cast_one,one_pow,mul_one]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_pow]
  ring

lemma familyRawScale_inverse_cap {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (Z X QK QP Lcap : ℝ) (hZ : 0<Z) (hX : 0<X) (hK : 0≤QK) (hP : 0≤QP)
    (hFcap : (Ideal.absNorm (∏ i,F.ideal i):ℝ)≤Z^Lcap)
    (hKcap : QK≤Z^Lcap) (hPcap : QP≤Z^Lcap) (hXcap : X⁻¹≤Z^Lcap) :
    (familyRawScale F s X QK QP)⁻¹≤
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)*Z^(7*Lcap) := by
  rw [familyRawScale_inverse]
  calc
    _ ≤ (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)*
        (Z^Lcap)^2*(Z^Lcap)^2*(Z^Lcap)^2*Z^Lcap := by gcongr
    _ = (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)*(Z^Lcap)^7 := by ring
    _ = _ := by
      rw [←Real.rpow_mul_natCast hZ.le]
      congr 2
      ring

theorem geometry_source_scale_cap {γ : Type*} [Fintype γ]
    (a c : γ→Eis) (mode : γ→Bool)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c i) (mode i))) :
    ∃ Z₀ : ℝ,1<Z₀ ∧ ∀ i : γ,∀ {φ : Type*} [Fintype φ] (F : PrimeFamily φ),
      ∀ Z X QK QP Lcap : ℝ,Z₀≤Z → 0<X → 0≤QK → 0≤QP →
      (Ideal.absNorm (∏ j,F.ideal j):ℝ)≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → X⁻¹≤Z^Lcap →
      (familyRawScale F (s i) X QK QP)⁻¹≤Z^(7*Lcap+1) := by
  let b := fun i => 27*(sourceCuspScale (s i).index)^2*(Ideal.absNorm (Ideal.span {c i}):ℝ)^2
  let Z₀ := (∑ i,b i)+2
  have hb : ∀ i,0≤b i := fun i => by dsimp only [b];positivity
  have hz : 1<Z₀ := by
    have hh := Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => hb i)
    dsimp only [Z₀]
    linarith
  refine ⟨Z₀,hz,?_⟩
  intro i φ _ F Z X QK QP Lcap hZ hX hK hP hFc hKc hPc hXc
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hz hZ)
  have hc : b i≤Z := by
    have hh : b i≤∑ j,b j := Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)
    dsimp only [Z₀] at hZ
    linarith
  apply (familyRawScale_inverse_cap F (s i) Z X QK QP Lcap hzpos hX hK hP hFc hKc hPc hXc).trans
  calc
    _ ≤ Z*Z^(7*Lcap) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hzpos.le _)
    _ = _ := by rw [Real.rpow_add hzpos,Real.rpow_one];ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1650

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CanonicalCaps.lean; sha256: f226c7541fb54ec75741e4a697344d925ac57116e2b96c56c375fa340ea95bd2 -/
section Source1651
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma canonical_mask_norm_cap (B F R : Ideal Eis) (Z V Q L : ℝ)
    (hZ : 1≤Z) (hB : (Ideal.absNorm B:ℝ)≤Z)
    (hF : (Ideal.absNorm F:ℝ)≤Z^V) (hR : (Ideal.absNorm R:ℝ)≤Z^Q)
    (hV : V≤L) (hQ : Q≤L) :
    (Ideal.absNorm (B*F*R):ℝ)≤Z^(2*L+1) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [map_mul,map_mul,Nat.cast_mul,Nat.cast_mul]
  calc
    _ ≤ Z*Z^V*Z^Q := mul_le_mul
      (mul_le_mul hB hF (Nat.cast_nonneg _) hz.le) hR (Nat.cast_nonneg _) (by positivity)
    _ = Z^(1+V+Q) := by rw [Real.rpow_add hz,Real.rpow_add hz,Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem canonical_actual_arithmetic_caps (L : ℝ) (hL : 0≤L)
    (J I B F R Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hB : B≠0) (hF : F≠0) (hR : R≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I)
    (hmask : rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R))
    (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
    (Z M V Q z N hhat QK QP : ℝ) (hZ : 2≤Z)
    (hBn : (Ideal.absNorm B:ℝ)≤Z)
    (hIn : (Ideal.absNorm I:ℝ)≤Z^M)
    (hFn : (Ideal.absNorm F:ℝ)≤Z^V)
    (hRn : (Ideal.absNorm R:ℝ)≤Z^Q)
    (hM : M≤L) (hV : V≤L) (hQ : Q≤L) (hz : z≤L)
    (hN : 0≤N) (hh : hhat≤L)
    (hK : QK≤2*Z^M) (hP : QP≤2*Z^z) :
    (Ideal.absNorm (∏ b : A,((poolPrimeFamily J (B*F*R) Q₀).restrict A).ideal b):ℝ)≤Z^(4*L+2) ∧
      QK≤Z^(4*L+2) ∧ QP≤Z^(4*L+2) ∧ (Z^(N-3*hhat))⁻¹≤Z^(4*L+2) := by
  have hZ1 : 1≤Z := by linarith
  have hZp : 0<Z := by linarith
  have hmaskn := canonical_mask_norm_cap B F R Z V Q L hZ1 hBn hFn hRn hV hQ
  have hfrozen := original_pool_restricted_cap J I (B*F*R) Q₀ hJ hI
    (mul_ne_zero (mul_ne_zero hB hF) hR) hpower hmask A Z M (2*L+1) hZp hIn hmaskn
  refine ⟨hfrozen.trans (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)),?_,?_,?_⟩
  · calc
      QK ≤ 2*Z^M := hK
      _ ≤ Z*Z^M := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hZp.le _)
      _ = Z^(M+1) := by rw [Real.rpow_add hZp,Real.rpow_one];ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  · calc
      QP ≤ 2*Z^z := hP
      _ ≤ Z*Z^z := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hZp.le _)
      _ = Z^(z+1) := by rw [Real.rpow_add hZp,Real.rpow_one];ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  · rw [←Real.rpow_neg hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1651

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CanonicalParameters.lean; sha256: f2c50e1a7d3431edfb0fd9532a0e13b755126e9dd560ed4e175b5f71539b9664 -/
section Source1652
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseMoment InverseTerminalWidths
noncomputable section

theorem canonical_reflection_parameters (L c η : ℝ)
    (hL : 0≤L) (hc : 0<c) (hη : 0<η) (hη1 : η≤1) (hηc : η≤c/100000) :
    ∃ ε ρ κ δ π : ℝ,0<ε ∧ 0<ρ ∧ 0<κ ∧ 0<δ ∧
      0≤δ+(7*L+1) ∧ η≤c/1000 ∧ δ+η≤c/1000 ∧ π≤c/1000 ∧
      ε*(L+L+2*(δ+(7*L+1)+η))+η/2≤π ∧ κ+ρ*L≤c/16 := by
  let ε := c/(100000*(L+1))
  let ρ := c/(64*(L+1))
  let κ := c/64
  refine ⟨ε,ρ,κ,η,c/1000,div_pos hc (by positivity),div_pos hc (by positivity),
    div_pos hc (by norm_num),hη,by positivity,by linarith,by linarith,le_refl _,?_,?_⟩
  · have hep : 0≤ε := (div_pos hc (by positivity : 0<100000*(L+1))).le
    have hed : ε*(L+1)=c/100000 := by dsimp [ε];field_simp
    have hb : L+L+2*(η+(7*L+1)+η)≤22*(L+1) := by linarith
    have hh := mul_le_mul_of_nonneg_left hb hep
    have he22 : ε*(22*(L+1))=22*(c/100000) := by calc
      _ = 22*(ε*(L+1)) := by ring
      _ = _ := by rw [hed]
    rw [he22] at hh
    linarith
  · have hrp : 0≤ρ := (div_pos hc (by positivity : 0<64*(L+1))).le
    have hrd : ρ*(L+1)=c/64 := by dsimp [ρ];field_simp
    have hb := mul_le_mul_of_nonneg_left (show L≤L+1 by linarith) hrp
    dsimp only [κ]
    rw [hrd] at hb
    linarith

lemma canonical_reflected_target_positive (F M Q z margin c O : ℝ)
    (h : CanonicalMargins F M Q z margin) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hc : 0<c) (hm : c/2≤margin) (hO : O≤M) :
    0<F-3*c/16-O/2 := by
  obtain ⟨hfirst,hsecond⟩ := h
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1652

/- Original source: OAI/NumberTheory/DirichletL/Reflection/RowReindex.lean; sha256: ed35237a94d74c754a9cdb6bfc23404b82f3683b1dab2a6e5de517b3c067f8e2 -/
section Source1653
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def originalResidualRows (rows : Finset (Ideal Eis)) (R Q : Ideal Eis) : Finset (Ideal Eis) :=
  (representativeRowFiber rows R Q).image (fun I => rowResidualPart I Q)

lemma originalResidualRows_reconstruct (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (K : Ideal Eis) (hK : K∈originalResidualRows rows R Q) :
    reconstructFiberRow R Q K∈representativeRowFiber rows R Q ∧
      rowResidualPart (reconstructFiberRow R Q K) Q=K := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  have he := reconstructFiberRow_of_original rows R Q I hI (hrows I (Finset.mem_filter.mp hI).1)
  rw [he]
  exact ⟨hI,rfl⟩

lemma originalResidualRows_range (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes, P∣Q) (X : ℝ)
    (hrows : ∀ I∈rows, I≠0 ∧ (Ideal.absNorm I:ℝ)≤X)
    (K : Ideal Eis) (hK : K∈originalResidualRows rows R Q) :
    Admissible K ∧ (Ideal.absNorm K:ℝ)≤
      X/((Ideal.absNorm (rowPowerfulPart R):ℝ)*(Ideal.absNorm (rowMaskPart R Q):ℝ)) := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  exact mem_idealRange.mp (completedRowFiber_residual_range rows Q (rowPowerfulPart R)
    (rowMaskPart R Q) hbad X hrows I hI)

theorem original_fiber_sum_reindex {M : Type*} [AddCommMonoid M]
    (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (f : Ideal Eis→M) :
    (∑ I∈representativeRowFiber rows R Q,f I)=
      ∑ K∈originalResidualRows rows R Q,f (reconstructFiberRow R Q K) := by
  rw [originalResidualRows,Finset.sum_image (representativeRowFiber_injective rows R Q hrows)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [reconstructFiberRow_of_original rows R Q I hI (hrows I (Finset.mem_filter.mp hI).1)]

theorem original_fiber_energy_reindex (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (f : Ideal Eis→ℂ) :
    (∑ I∈representativeRowFiber rows R Q,‖f I‖^2)=
      ∑ K∈originalResidualRows rows R Q,‖f (reconstructFiberRow R Q K)‖^2 :=
  original_fiber_sum_reindex rows R Q hrows (fun I => ‖f I‖^2)

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1653

/- Original source: OAI/NumberTheory/DirichletL/Reflection/FixedTuples.lean; sha256: 960abc7cd14c547bfbd32ba10e8cc1fd9d4500a22473edd06a624332fc2f4ca2 -/
section Source1654
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def fixedSlotTupleSet (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) : Finset (σ→Ideal Eis) :=
  (Fintype.piFinset L).filter fun p => ∀ j i,p i≠F j

lemma mem_fixedSlotTupleSet (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (p : σ→Ideal Eis) :
    p∈fixedSlotTupleSet L F ↔ (∀ i,p i∈L i) ∧ ∀ j i,p i≠F j := by
  simp only [fixedSlotTupleSet,Finset.mem_filter,Fintype.mem_piFinset]

lemma fixedSlotTupleSet_product_injective (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P) :
    Set.InjOn slotTupleProduct (↑(fixedSlotTupleSet L F) : Set (σ→Ideal Eis)) :=
  (slotTupleProduct_injective_on L hL hprime).mono (fun p hp => (mem_fixedSlotTupleSet L F p).mp hp |>.1)

def supportedSlotTupleEquiv (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (K : Ideal Eis) :
    supportedSlotChoices L F K ≃ {p : fixedSlotTupleSet L F // IsCoprime K (slotTupleProduct p.val)} where
  toFun p := ⟨⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩⟩,p.property.1⟩
  invFun p := ⟨fun i => ⟨p.val.val i,((mem_fixedSlotTupleSet L F _).mp p.val.property).1 i⟩,
    ⟨p.property,((mem_fixedSlotTupleSet L F _).mp p.val.property).2⟩⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    rfl
  right_inv p := rfl

def supportedSlotProductEquiv (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (K : Ideal Eis) :
    supportedSlotChoices L F K ≃
      {P : (fixedSlotTupleSet L F).image slotTupleProduct // IsCoprime K P.val} := by
  let f := fun p : supportedSlotChoices L F K =>
    (⟨⟨slotTupleProduct (fun i => (p.val i).val),Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩,p.property.1⟩ :
      {P : (fixedSlotTupleSet L F).image slotTupleProduct // IsCoprime K P.val})
  apply Equiv.ofBijective f
  constructor
  · intro p q he
    have hv := congrArg (fun P => P.val.val) he
    have hh := fixedSlotTupleSet_product_injective L F hL hprime
      ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩)
      ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (q.val i).property,q.property.2⟩) hv
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun hh i)
  · intro P
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp P.val.property
    let q : supportedSlotChoices L F K := ⟨fun i => ⟨p i,((mem_fixedSlotTupleSet L F p).mp hp).1 i⟩,
      ⟨by change IsCoprime K (slotTupleProduct p);rw [he];exact P.property,((mem_fixedSlotTupleSet L F p).mp hp).2⟩⟩
    refine ⟨q,?_⟩
    apply Subtype.ext
    exact Subtype.ext he

lemma supportedSlotProductEquiv_apply (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (K : Ideal Eis) (p : supportedSlotChoices L F K) :
    ((supportedSlotProductEquiv L F hL hprime K) p).val.val=∏ i,(p.val i).val := rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1654

/- Original source: OAI/NumberTheory/DirichletL/Reflection/TupleDyads.lean; sha256: f32fa9c04e86386e2d49937029abc3c758596f3ee35366bfed565ffa96a37efa -/
section Source1655
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def activeTupleDyad (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (i : Fin (columnDyadicLength H+1)) : Finset (σ→Ideal Eis) :=
  tuples.filter fun p => divisorDyadicLabel H (slotTupleProduct p)=i

omit [DecidableEq σ] in
lemma sum_activeTupleDyads {A : Type*} [AddCommMonoid A]
    (tuples : Finset (σ→Ideal Eis)) (H : ℝ) (f : (σ→Ideal Eis)→A) :
    (∑ p∈tuples,f p)=∑ i : Fin (columnDyadicLength H+1),∑ p∈activeTupleDyad tuples H i,f p := by
  exact (Finset.sum_fiberwise tuples (fun p => divisorDyadicLabel H (slotTupleProduct p)) f).symm

omit [DecidableEq σ] in
lemma activeTupleDyad_bounds (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (p : σ→Ideal Eis) (hp : p∈activeTupleDyad tuples H i) :
    divisorDyadicScale i.val≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
      (Ideal.absNorm (slotTupleProduct p):ℝ)≤2*divisorDyadicScale i.val := by
  obtain ⟨hpt,he⟩ := Finset.mem_filter.mp hp
  have hh := divisorDyadicLabel_bounds H (slotTupleProduct p) (hn p hpt).1 (hn p hpt).2
  rw [he] at hh
  constructor
  · exact max_le (hn p hpt).1 hh.1.le
  · have ht : (2:ℝ)^i.val/2≤divisorDyadicScale i.val := le_max_right _ _
    linarith [hh.2]

omit [DecidableEq σ] in
lemma activeTupleDyad_scale_le (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    divisorDyadicScale i.val≤H := by
  obtain ⟨p,hp⟩ := hi
  exact (activeTupleDyad_bounds tuples H hn i p hp).1.trans (hn p (Finset.mem_filter.mp hp).1).2

omit [DecidableEq σ] in
lemma activeTupleDyad_width (tuples : Finset (σ→Ideal Eis)) (H Z z : ℝ)
    (hZ : 1<Z) (hH : H≤Z^z)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    0≤Real.logb Z (divisorDyadicScale i.val) ∧ Real.logb Z (divisorDyadicScale i.val)≤z := by
  have hs := divisorDyadicScale_ge_one i.val
  have hp : 0<divisorDyadicScale i.val := lt_of_lt_of_le zero_lt_one hs
  constructor
  · have hh := Real.logb_le_logb_of_le hZ zero_lt_one hs
    simpa only [Real.logb_one] using hh
  · have hh := Real.logb_le_logb_of_le hZ hp ((activeTupleDyad_scale_le tuples H hn i hi).trans hH)
    rwa [Real.logb_rpow (lt_trans zero_lt_one hZ) (ne_of_gt hZ)] at hh
omit [DecidableEq σ] in
lemma slotTupleProduct_norm_bound (L : σ→Finset (Ideal Eis)) (H : σ→ℝ)
    (hzero : ∀ i,∀ P∈L i,P≠0) (hH : ∀ i,∀ P∈L i,(Ideal.absNorm P:ℝ)≤H i)
    (p : σ→Ideal Eis) (hp : ∀ i,p i∈L i) :
    1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤∏ i,H i := by
  have hn : slotTupleProduct p≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hzero i _ (hp i))
  refine ⟨QuadraticMainBoundary.norm_one_le hn,?_⟩
  change (Ideal.absNorm (∏ i,p i):ℝ)≤_
  rw [map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hH i _ (hp i))

omit [DecidableEq σ] in
lemma activeTupleDyad_energy_scale (tuples : Finset (σ→Ideal Eis)) (H Z z : ℝ)
    (hZ : 1<Z) (hH : H≤Z^z)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    2≤2*divisorDyadicScale i.val ∧
      0≤Real.logb Z ((2*divisorDyadicScale i.val)/2) ∧
      Real.logb Z ((2*divisorDyadicScale i.val)/2)≤z ∧
      ∀ p∈activeTupleDyad tuples H i,
        (2*divisorDyadicScale i.val)/2≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
          (Ideal.absNorm (slotTupleProduct p):ℝ)≤2*divisorDyadicScale i.val := by
  have hw := activeTupleDyad_width tuples H Z z hZ hH hn i hi
  have hs := divisorDyadicScale_ge_one i.val
  rw [show (2*divisorDyadicScale i.val)/2=divisorDyadicScale i.val by ring]
  exact ⟨by linarith,hw.1,hw.2,activeTupleDyad_bounds tuples H hn i⟩

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1655

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalCellBounds.lean; sha256: 977f088549218a897986d0381623c113530b604988899b0f99e0c49354130041 -/
section Source1656
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma original_residual_norm_bounds (rows : Finset (Ideal Eis)) (J Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (U : ℝ)
    (hrows : ∀ I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) :
    ∀ K∈originalResidualRows rows J Q,
      1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤
        U/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ)) := by
  intro K hK
  have hr := originalResidualRows_range rows J Q hbad U hrows K hK
  exact ⟨QuadraticMainBoundary.norm_one_le hr.1.1,hr.2⟩

theorem original_residual_cell_representative (rows : Finset (Ideal Eis)) (J Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (U : ℝ)
    (hrows : ∀ I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U)
    (H : ℝ) (hH : H=U/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ)))
    (i : Fin (columnDyadicLength H+1))
    (hi : (divisorDyadicBin (originalResidualRows rows J Q) H i).Nonempty) :
    ∃ I∈rows,I≠0 ∧ rowPowerfulPart J=rowPowerfulPart I ∧ rowMaskPart J Q=rowMaskPart I Q ∧
      (Ideal.absNorm I:ℝ)≤U ∧
      divisorDyadicScale i.val≤(Ideal.absNorm (rowResidualPart I Q):ℝ) ∧
      (Ideal.absNorm (rowResidualPart I Q):ℝ)≤2*divisorDyadicScale i.val := by
  obtain ⟨K,hK⟩ := hi
  have hKT := (Finset.mem_filter.mp hK).1
  have hr := originalResidualRows_reconstruct rows J Q (fun I hI => (hrows I hI).1) K hKT
  obtain ⟨hI,hp,hm⟩ := Finset.mem_filter.mp hr.1
  refine ⟨reconstructFiberRow J Q K,hI,(hrows _ hI).1,hp.symm,hm.symm,(hrows _ hI).2,?_⟩
  rw [hr.2]
  apply divisorDyadicBin_bounds _ H _ i K hK
  intro D hD
  rw [hH]
  exact original_residual_norm_bounds rows J Q hbad U hrows D hD

lemma original_residual_cell_scale_cap (rows : Finset (Ideal Eis)) (J Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (U H Z L : ℝ)
    (hrows : ∀ I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U)
    (hH : H=U/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ)))
    (hZ : 2≤Z) (hcap : H≤Z^L)
    (i : Fin (columnDyadicLength H+1))
    (hi : (divisorDyadicBin (originalResidualRows rows J Q) H i).Nonempty) :
    1≤2*divisorDyadicScale i.val ∧ 2*divisorDyadicScale i.val≤Z^(L+1) := by
  have hz : 0<Z := by linarith
  have hs := divisorDyadicScale_ge_one i.val
  have hh : divisorDyadicScale i.val≤H := by
    apply divisorDyadicBin_scale_le _ H _ i hi
    intro D hD
    rw [hH]
    exact original_residual_norm_bounds rows J Q hbad U hrows D hD
  refine ⟨by linarith,?_⟩
  calc
    _ ≤ Z*Z^L := mul_le_mul hZ (hh.trans hcap) (by linarith) hz.le
    _ = _ := by rw [Real.rpow_add hz,Real.rpow_one];ring

lemma dyadic_canonical_lower (Z QK : ℝ) (hZ : 1<Z) (hQK : 0<QK)
    (K : Ideal Eis) (hK : QK/2≤(Ideal.absNorm K:ℝ)) :
    Z^(Real.logb Z QK)/2≤(Ideal.absNorm K:ℝ) := by
  rw [Real.rpow_logb (lt_trans zero_lt_one hZ) (ne_of_gt hZ) hQK]
  exact hK

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1656

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CanonicalEnergy.lean; sha256: c5e330498d8281b6574cfd7c8d18cd85a5f6f7e6c89611673bbba307b410cf78 -/
section Source1657
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem canonical_member_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (hB : B≠0) (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J I F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z N V M z₀ margin O₀ hhat d QK QP : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm I:ℝ)≤Z^M → (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      QK/2≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      1≤QK → QK≤2*Z^M → 2≤QP → QP/2≤Z^z₀ →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ (Z^(N-3*hhat)) r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O₀/2) := by
  let Lcap := 4*L+2
  have hLc : 0≤Lcap := by dsimp [Lcap];positivity
  obtain ⟨ε,ρ,κ,δ,π,hε,hρ,hκ,hδ,hδL,hηsmall,hδη,hπ,hbudget,hsmall⟩ :=
    canonical_reflection_parameters Lcap cstar η hLc hcstar hη hη1 hηc
  obtain ⟨degree,C,Z₁,hC,hZ₁,henergy⟩ := original_member_geometry_uniform a c₀ mode
    ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hη
    κ δ (7*Lcap+1) Lcap hκ hδL hLc Lcap 1 hδ
  obtain ⟨Z₂,hZ₂,hscale⟩ := geometry_source_scale_cap a c₀ mode s
  obtain ⟨Z₃,hZ₃,hwidth⟩ := width_error_threshold B hB 1 1 2 1 η
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hη
  obtain ⟨Z₄,hZ₄,hlog⟩ := constant_log_error 16 η (by norm_num) hη
  let Z₀ := max Z₁ (max Z₂ (max Z₃ (max Z₄ (max 2 (Ideal.absNorm B:ℝ)))))
  have hz1 : Z₁≤Z₀ := le_max_left _ _
  have hz2 : Z₂≤Z₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hz3 : Z₃≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hz4 : Z₄≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hz5 : max 2 (Ideal.absNorm B:ℝ)≤Z₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨degree,C,Z₀,hC,hZ₁.trans_le hz1,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F R Q₀ hJ hI hF hR hpower hmask A
    Z N V M z₀ margin O₀ hhat d QK QP hZ hN hM hMc hVc hzc hhc
    hIn hFn hRn hO hOM hOn hKr hK1 hKc hP2 hPc hinv hmargin hVd hhd hd
  have hZ1 : 1<Z := lt_of_lt_of_le hZ₁ (hz1.trans hZ)
  have hZp : 0<Z := lt_trans zero_lt_one hZ1
  have hZ2 : 2≤Z := (le_max_left _ _).trans (hz5.trans hZ)
  have hBn : (Ideal.absNorm B:ℝ)≤Z := (le_max_right _ _).trans (hz5.trans hZ)
  have hKp : 0<QK := lt_of_lt_of_le zero_lt_one hK1
  have hPp : 0<QP := by linarith
  have hPc' : QP≤2*Z^z₀ := by linarith
  obtain ⟨hFc,hKcap,hPcap,hXi⟩ := canonical_actual_arithmetic_caps L hL
    J I B F R Q₀ hJ hI hB hF hR hpower hmask A
    Z M V L z₀ N hhat QK QP hZ2 hBn hIn hFn hRn hMc hVc (le_refl _) hzc hN hhc hKc hPc'
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hXp : 0<Z^(N-3*hhat) := Real.rpow_pos_of_pos hZp _
  have hsc := hscale i G Z (Z^(N-3*hhat)) QK QP Lcap (hz2.trans hZ)
    hXp hKp.le hPp.le hFc hKcap hPcap hXi
  have hw := hwidth Z (hz3.trans hZ)
  have hza : 0≤Real.logb Z (QP/2) := Real.logb_nonneg hZ1 (by linarith)
  have hzac : Real.logb Z (QP/2)≤z₀ := by
    have he := Real.logb_le_logb_of_le hZ1 (by linarith : 0<QP/2) hPc
    rwa [Real.logb_rpow hZp (ne_of_gt hZ1)] at he
  have hzt : 0≤z₀ := hza.trans hzac
  have ht := canonical_reflected_target_positive (N+V) M (normWidth Z R) z₀ margin cstar O₀
    hinv hM (normWidth_nonneg Z hZ1 R hR) hzt hcstar hmargin hOM
  have hc := henergy i (σ:=σ) J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z (N+V) N V M z₀ margin cstar O₀ (Real.logb Z QK) (Real.logb Z (QP/2))
    (N-3*hhat) hhat d π 1 1 2 1 (Z^(N-3*hhat)) QK QP Lcap Lcap
    (hz1.trans hZ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hXp hKp hPp
    (by simpa using hIn) (by simpa using hOn) (dyadic_canonical_lower Z QK hZ1 hKp _ hKr)
    (by simpa using hFn) hw.1 hw.2 hinv rfl rfl hVd hhd rfl rfl
    (by rw [Real.logb_rpow hZp (ne_of_gt hZ1)]) hM hO hza hzac hcstar hmargin hd
    hηsmall hδη hπ hKcap (by linarith : QP/2≤Z^Lcap)
    (hlog Z (hz4.trans hZ)) hbudget hXi hKcap hPcap (by linarith : -1≤N+V-3*cstar/16-O₀/2)
    hFc hsc hFc hsmall
  exact hc
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1657

/- Original source: OAI/NumberTheory/DirichletL/Reflection/DyadSelection.lean; sha256: af7bd81db95d88b04f98c372ee0cec3af00ed9010d50dcb73cd1c64044a76d95 -/
section Source1658
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] [DecidableEq σ] {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)

omit [DecidableEq σ] in
lemma activeTupleDyad_subset (i : Fin (columnDyadicLength Hslot+1)) : activeTupleDyad tuples Hslot i⊆tuples :=
  Finset.filter_subset _ _

lemma divisorDyadicBin_subset (i : Fin (columnDyadicLength Hrow+1)) : divisorDyadicBin rows Hrow i⊆rows :=
  Finset.filter_subset _ _

variable (C : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode)

def dyadicTupleControlled (K : rows) (p : tuples) (hp : IsCoprime K.val (slotTupleProduct p.val)) :
    ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
      (memberTupleFamily tuples hmax hgood p)).generator N a c mode :=
  C (divisorDyadicLabel Hrow K.val) (divisorDyadicLabel Hslot (slotTupleProduct p.val))
    ⟨K.val,Finset.mem_filter.mpr ⟨K.property,rfl⟩⟩ ⟨p.val,Finset.mem_filter.mpr ⟨p.property,rfl⟩⟩ hp

omit [DecidableEq σ] in
lemma dyadicTupleControlled_at (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1))
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j)
    (hp : IsCoprime K.val (slotTupleProduct p.val)) :
    dyadicTupleControlled G rows hrows tuples hmax hgood Hrow Hslot C
      ⟨K.val,divisorDyadicBin_subset rows Hrow i K.property⟩
      ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩ hp=C i j K p hp := by
  rcases K with ⟨K,hK⟩
  rcases p with ⟨p,hpT⟩
  have hi := (Finset.mem_filter.mp hK).2
  have hj := (Finset.mem_filter.mp hpT).2
  subst i
  subst j
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1658

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SlotMass.lean; sha256: bf21c509f4cc448b9a68d771f0e7b75ebb123fa1c5c8ea6f5bd54e70aef082ab -/
section Source1659
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma inactive_choices_mass (L : σ→Finset (Ideal Eis)) (T : Finset σ) :
    (∑ b : ∀ i : {i // i∉T}, L i.val,
      ‖∏ i : {i // i∉T}, (Ideal.absNorm (b i).val:ℂ)⁻¹‖)=
    ∏ i : {i // i∉T}, ∑ P∈L i.val, (Ideal.absNorm P:ℝ)⁻¹ := by
  simp only [norm_prod,norm_inv,Complex.norm_natCast]
  refine (Fintype.prod_sum (fun (i : {i // i∉T}) (P : L i.val) => (Ideal.absNorm P.val:ℝ)⁻¹)).symm.trans ?_
  apply Finset.prod_congr rfl
  intro i hi
  exact Finset.sum_coe_sort (L i.val) (fun P => (Ideal.absNorm P:ℝ)⁻¹)

lemma inactive_choices_mass_bound (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (H : σ→ℝ) (hzero : ∀ i, ∀ P∈L i, P≠0)
    (hH : ∀ i, ∀ P∈L i, (Ideal.absNorm P:ℝ)≤H i) :
    (∑ b : ∀ i : {i // i∉T}, L i.val,
      ‖∏ i : {i // i∉T}, (Ideal.absNorm (b i).val:ℂ)⁻¹‖)≤
      ∏ i : {i // i∉T}, 256*(columnDyadicLength (H i.val)+1:ℝ) := by
  rw [inactive_choices_mass]
  apply Finset.prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    simpa only [one_div] using finite_inverse_norm_sum (L i.val) (H i.val) (hzero i.val) (hH i.val)

theorem original_inactive_choices_energy {κ : Type*}
    (L : σ→Finset (Ideal Eis)) (T : Finset σ) (rows : Finset κ)
    (H : σ→ℝ) (hzero : ∀ i, ∀ P∈L i, P≠0)
    (hH : ∀ i, ∀ P∈L i, (Ideal.absNorm P:ℝ)≤H i)
    (f : (∀ i, L i)→κ→ℂ) (E : ℝ) (hE : 0≤E)
    (hf : ∀ b : ∀ i : {i // i∉T}, L i.val,
      (∑ k∈rows, ‖∑ a : ∀ i : T, L i.val, f ((slotChoiceSplit L T).symm (a,b)) k‖^2)≤E) :
    (∑ k∈rows, ‖∑ p : ∀ i, L i,
      (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p i).val:ℂ)⁻¹)*f p k‖^2)≤
    (∏ i : {i // i∉T}, 256*(columnDyadicLength (H i.val)+1:ℝ))^2*E := by
  simp_rw [sum_slot_choices L T]
  apply (weighted_finite_row_energy_uniform Finset.univ rows
    (fun b : ∀ i : {i // i∉T}, L i.val => ∏ i, (Ideal.absNorm (b i).val:ℂ)⁻¹)
    (fun b k => ∑ a : ∀ i : T, L i.val, f ((slotChoiceSplit L T).symm (a,b)) k)
    E (fun b hb => hf b)).trans
  apply mul_le_mul_of_nonneg_right _ hE
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun b hb => norm_nonneg _))
    (inactive_choices_mass_bound L T H hzero hH) 2
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1659

/- Original source: OAI/NumberTheory/DirichletL/Reflection/InactiveRows.lean; sha256: 930dc38ffbfb89e55066a653e1639b5dc122bf36f2913aee4661b3775ecbbd6a -/
section Source1660
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def inactiveRowSet (rows : Finset (Ideal Eis)) (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (F : φ→Ideal Eis) (b : ∀ i : {i // i∉T},L i.val) : Finset (Ideal Eis) :=
  rows.filter fun K => IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠F j

lemma subtype_zero_extension_energy {κ : Type*} [DecidableEq κ]
    (rows small : Finset κ) (hs : small⊆rows) (f : small→ℂ) :
    (∑ k∈rows,‖if hk:k∈small then f ⟨k,hk⟩ else 0‖^2)=∑ k : small,‖f k‖^2 := by
  have he : (∑ k∈rows,‖if hk:k∈small then f ⟨k,hk⟩ else 0‖^2)=
      ∑ k∈small,‖if hk:k∈small then f ⟨k,hk⟩ else 0‖^2 := by
    symm
    apply Finset.sum_subset hs
    intro k hk hks
    simp only [dite_eq_right hks,norm_zero,zero_pow (by decide : (2:ℕ)≠0)]
  rw [he,←Finset.sum_coe_sort small]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dite_eq_left k.property]

theorem original_inactive_restricted_energy
    (rows : Finset (Ideal Eis)) (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (F : φ→Ideal Eis) (H : σ→ℝ)
    (hzero : ∀ i,∀ P∈L i,P≠0) (hH : ∀ i,∀ P∈L i,(Ideal.absNorm P:ℝ)≤H i)
    (w : ∀ i,L i→ℂ) (hw : ∀ i P,‖w i P‖≤1)
    (f : ∀ b : ∀ i : {i // i∉T},L i.val,inactiveRowSet rows L T F b→ℂ)
    (E : ℝ) (hE : 0≤E)
    (hf : ∀ b,(∑ k : inactiveRowSet rows L T F b,‖f b k‖^2)≤E) :
    (∑ k∈rows,‖∑ b : ∀ i : {i // i∉T},L i.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i)))*
        (if hk:k∈inactiveRowSet rows L T F b then f b ⟨k,hk⟩ else 0)‖^2)≤
    (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*E := by
  let wt := fun b : ∀ i : {i // i∉T},L i.val =>
    (∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i))
  let g := fun (b : ∀ i : {i // i∉T},L i.val) k =>
    if hk:k∈inactiveRowSet rows L T F b then f b ⟨k,hk⟩ else 0
  have hg (b) : (∑ k∈rows,‖g b k‖^2)≤E := by
    rw [show (∑ k∈rows,‖g b k‖^2)=∑ k : inactiveRowSet rows L T F b,‖f b k‖^2 from
      subtype_zero_extension_energy rows _ (Finset.filter_subset _ _) (f b)]
    exact hf b
  have hm : (∑ b,‖wt b‖)≤∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ) := by
    apply (Finset.sum_le_sum (fun b hb => ?_)).trans (inactive_choices_mass_bound L T H hzero hH)
    change ‖_*_‖≤_
    rw [norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact slot_coefficient_norm (fun i : {i // i∉T} => L i.val) (fun i => w i.val) (fun i => hw i.val) b
  apply (weighted_finite_row_energy_uniform Finset.univ rows wt g E (fun b hb => hg b)).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun b _ => norm_nonneg _)) hm 2) hE
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1660

/- Original source: OAI/NumberTheory/DirichletL/Reflection/DyadReassembly.lean; sha256: eaf2d0276cf3f3189af7c5a4af383a3b18ff69db32e9ecd0d67598d3a44760b4 -/
section Source1661
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma dependent_sum_filter_partition {α β A : Type*} [Fintype β] [DecidableEq β] [AddCommMonoid A]
    (T : Finset α) (label : α→β) (f : T→A) :
    (∑ p : T,f p)=∑ j : β,∑ p : T.filter (fun p => label p=j),f ⟨p.val,(Finset.mem_filter.mp p.property).1⟩ := by
  let g : α→A := fun p => if hp:p∈T then f ⟨p,hp⟩ else 0
  have h := Finset.sum_fiberwise T label g
  calc
    _ = ∑ p∈T,g p := by
      symm
      rw [←Finset.sum_coe_sort T]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [g,dite_eq_left p.property]
    _ = ∑ j,∑ p∈T.filter (fun p => label p=j),g p := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [←Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [g,dite_eq_left (Finset.mem_filter.mp p.property).1]

theorem dependent_partition_energy {α β ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rows : Finset α) (tuples : Finset β) (rowLabel : α→ι) (slotLabel : β→κ)
    (f : rows→tuples→ℂ) :
    (∑ k : rows,‖∑ p : tuples,f k p‖^2)≤
      (Fintype.card κ:ℝ)*∑ i : ι,∑ j : κ,
        ∑ k : rows.filter (fun k => rowLabel k=i),
          ‖∑ p : tuples.filter (fun p => slotLabel p=j),
            f ⟨k.val,(Finset.mem_filter.mp k.property).1⟩
              ⟨p.val,(Finset.mem_filter.mp p.property).1⟩‖^2 := by
  rw [dependent_sum_filter_partition rows rowLabel]
  calc
    _ ≤ ∑ i : ι,(Fintype.card κ:ℝ)*∑ j : κ,
        ∑ k : rows.filter (fun k => rowLabel k=i),
          ‖∑ p : tuples.filter (fun p => slotLabel p=j),
            f ⟨k.val,(Finset.mem_filter.mp k.property).1⟩
              ⟨p.val,(Finset.mem_filter.mp p.property).1⟩‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      let g := fun (j : κ) (k : rows.filter (fun k => rowLabel k=i)) =>
        ∑ p : tuples.filter (fun p => slotLabel p=j),
          f ⟨k.val,(Finset.mem_filter.mp k.property).1⟩ ⟨p.val,(Finset.mem_filter.mp p.property).1⟩
      have he := weighted_finite_row_energy (Finset.univ : Finset κ)
        (Finset.univ : Finset (rows.filter (fun k => rowLabel k=i))) (fun _ => (1:ℂ)) g
      simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at he
      convert he using 1
      apply Finset.sum_congr rfl
      intro k hk
      congr 2
      exact dependent_sum_filter_partition tuples slotLabel _
    _ = _ := by rw [Finset.mul_sum]

variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)
variable (C : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode)
variable (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ)

def dyadicPhysicalTerm (K : rows) (p : tuples) : ℂ :=
  if hp:IsCoprime K.val (slotTupleProduct p.val) then
    r K.val*aw p.val*mixedReflectedValue
      (dyadicTupleControlled G rows hrows tuples hmax hgood Hrow Hslot C K p hp) s
      (G.reflected K.val (hrows K.val K.property) (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
      (G.reflected K.val (hrows K.val K.property) (memberTupleFamily tuples hmax hgood p)).generator_good
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0

lemma dyadicPhysicalTerm_at (i : Fin (columnDyadicLength Hrow+1))
    (j : Fin (columnDyadicLength Hslot+1))
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j) :
    dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw
      ⟨K.val,divisorDyadicBin_subset rows Hrow i K.property⟩
      ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩=
    if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue (C i j K p hp) s
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0 := by
  unfold dyadicPhysicalTerm
  split_ifs with hp
  · rw [dyadicTupleControlled_at]
  · rfl

theorem dyadic_physical_energy (E : ℝ)
    (hE : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      (∑ K : rows.filter (fun K => divisorDyadicLabel Hrow K=i),
        ‖∑ p : tuples.filter (fun p => divisorDyadicLabel Hslot (slotTupleProduct p)=j),
          dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw
            ⟨K.val,(Finset.mem_filter.mp K.property).1⟩
            ⟨p.val,(Finset.mem_filter.mp p.property).1⟩‖^2)≤E) :
    (∑ K : rows,‖∑ p : tuples,
      dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw K p‖^2)≤
      (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*E := by
  have he := dependent_partition_energy rows tuples (divisorDyadicLabel Hrow)
    (fun p => divisorDyadicLabel Hslot (slotTupleProduct p))
    (dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw)
  apply he.trans
  have hb := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hE i j))
  apply (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Fintype.card (Fin (columnDyadicLength Hslot+1))))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1661

/- Original source: OAI/NumberTheory/DirichletL/Reflection/DyadCompletionEnergy.lean; sha256: d3105a7b3e83afd1269d82041fff2c8ac194bf67f3f06772fc5131d002edfb20 -/
section Source1662
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)

abbrev CellCompletion (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1)) :=
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode

variable (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : φ→ℕ) (W : ℝ→ℂ) (X : ℝ)

def cellPhysicalTerm (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1))
    (D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j)
    (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ)
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j) : ℂ :=
    if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue (D K p hp) s
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0

theorem physical_dyad_selection_energy (E : ℝ→ℝ) (hE : ∀ θ,0≤E θ)
    (he : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      (divisorDyadicBin rows Hrow i).Nonempty → (activeTupleDyad tuples Hslot j).Nonempty →
      ∃ D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)≤E θ) :
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : rows,‖∑ p : tuples,
          dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw K p‖^2)≤
          (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*E θ := by
  have hall : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      ∃ D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)≤E θ := by
    intro i j
    by_cases hi : (divisorDyadicBin rows Hrow i).Nonempty
    · by_cases hj : (activeTupleDyad tuples Hslot j).Nonempty
      · exact he i j hi hj
      · let D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j :=
          fun K p hp => (hj ⟨p.val,p.property⟩).elim
        refine ⟨D,?_⟩
        intro θ r aw hr haw
        have hzero : ∀ K : divisorDyadicBin rows Hrow i,
            (∑ p : activeTupleDyad tuples Hslot j,
              cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p)=0 := by
          intro K
          apply Finset.sum_eq_zero
          intro p hp
          exact (hj ⟨p.val,p.property⟩).elim
        simp_rw [hzero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),Finset.sum_const_zero]
        exact hE θ
    · let D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j :=
        fun K p hp => (hi ⟨K.val,K.property⟩).elim
      refine ⟨D,?_⟩
      intro θ r aw hr haw
      have hzero : (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)=0 := by
        apply Finset.sum_eq_zero
        intro K hK
        exact (hi ⟨K.val,K.property⟩).elim
      rw [hzero]
      exact hE θ
  choose D hD using hall
  refine ⟨D,?_⟩
  intro θ r aw hr haw
  apply dyadic_physical_energy G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw (E θ)
  intro i j
  have hid : (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
      dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw
        ⟨K.val,divisorDyadicBin_subset rows Hrow i K.property⟩
        ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩‖^2)=
      ∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
        cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j (D i j) θ r aw K p‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    apply congrArg (fun z : ℂ => ‖z‖^2)
    apply Finset.sum_congr rfl
    intro p hp
    exact dyadicPhysicalTerm_at G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw i j K p
  exact hid.trans_le (hD i j θ r aw hr haw)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1662

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CanonicalDyads.lean; sha256: e7cefc5b486ade4cddcdf58febcdd9c522697865bf397ec195839e3422faf6f0 -/
section Source1663
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem canonical_dyadic_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (hB : B≠0) (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0) (_hR : R≠0),
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z N V M z₀ margin O₀ hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
      let Hrow := Z^M/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J (B*F*R)):ℝ))
      let Hslot := Z^z₀
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (tuples : Finset (σ→Ideal Eis))
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (_hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hmax hgood p)).ideal)) →
      (∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)) →
      (∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)≠2) →
      (∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot) →
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g) G rows hrows tuples hmax hgood Hrow Hslot i j,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖∑ p : tuples,
        dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D (s g) (hc₀ g) jF W θ (Z^(N-3*hhat)) r aw K p‖^2)≤
        (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*
          (C*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O₀/2)) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_member_geometry_uniform a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac B hB L cstar η hL hcstar hη hη1 hηc
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro g σ _ _ J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents hsub hbad
  dsimp only
  intro tuples hmax hgood hinj hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let Hrow := Z^M/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J (B*F*R)):ℝ))
  let Hslot := Z^z₀
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let jF := fun b : A => completedLocalExponent J F b.val.val
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzp : 0<Z := lt_trans zero_lt_one hz
  have hrowNorm : ∀ K∈rows,1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤Hrow :=
    fun K hK => original_residual_norm_bounds parents J (B*F*R) hbad (Z^M) hparents K (hsub hK)
  have htupleNorm : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
      (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot := fun p hp =>
    ⟨QuadraticMainBoundary.norm_one_le (primaryGenerator_ne_zero_ideal _ (hPnorm p hp).1.2),(hPnorm p hp).2⟩
  apply physical_dyad_selection_energy G rows hrows tuples hmax hgood Hrow Hslot
    (s g) (hc₀ g) jF W (Z^(N-3*hhat)) (fun θ => C*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O₀/2))
    (fun θ => by positivity)
  intro i j hi hj
  let Rc := divisorDyadicBin rows Hrow i
  let Tc := activeTupleDyad tuples Hslot j
  let hm := fun p hp k => hmax p (activeTupleDyad_subset tuples Hslot j hp) k
  let hg := fun p hp k => hgood p (activeTupleDyad_subset tuples Hslot j hp) k
  have hTc : Tc.Nonempty := hj
  have hRi : ∀ K∈Rc,Admissible K := fun K hK => hrows K (divisorDyadicBin_subset rows Hrow i hK)
  have hti : Set.InjOn slotTupleProduct (↑Tc : Set (σ→Ideal Eis)) :=
    hinj.mono (activeTupleDyad_subset tuples Hslot j)
  have hKr := divisorDyadicBin_bounds rows Hrow hrowNorm i
  have hPr := activeTupleDyad_bounds tuples Hslot htupleNorm j
  obtain ⟨K,hK⟩ := hi
  obtain ⟨I,hI,heI⟩ := Finset.mem_image.mp (hsub (divisorDyadicBin_subset rows Hrow i hK))
  obtain ⟨hIp,hpow,hmask⟩ := Finset.mem_filter.mp hI
  have hI0 := (hparents I hIp).1
  have hIn := (hparents I hIp).2
  have hKlower : (2*divisorDyadicScale i.val)/2≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) := by
    rw [heI]
    convert (hKr K hK).1 using 1 ; ring
  have hKupper : 2*divisorDyadicScale i.val≤2*Z^M := by
    have hres : (Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ)≤(Ideal.absNorm I:ℝ) := by
      rw [rowResidualPart_norm I (B*F*R) hI0]
      apply div_le_self (Nat.cast_nonneg _)
      exact one_le_mul_of_one_le_of_one_le
        (QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero I))
        (QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart I) (B*F*R)))
    have hs := hKlower.trans (hres.trans hIn)
    linarith
  have hPupper : (2*divisorDyadicScale j.val)/2≤Z^z₀ := by
    convert activeTupleDyad_scale_le tuples Hslot htupleNorm j hj using 1 ; dsimp [Hslot] ; ring
  let S := tuplePrimeFamily Tc hTc hm hg
  have hScop : ∀ P∈Tc.image slotTupleProduct,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal) := by
    intro P hP
    exact hpair ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  have hSN : ∀ P∈Tc.image slotTupleProduct,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b) := by
    intro P hP
    exact hPN ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  have hSchar : ∀ P∈Tc.image slotTupleProduct,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2 := by
    intro P hP
    exact hPchar ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  obtain ⟨D,hD⟩ := he g J I F R Q₀ hJ hI0 hF hR hpow.symm hmask.symm A
    Z N V M z₀ margin O₀ hhat d (2*divisorDyadicScale i.val) (2*divisorDyadicScale j.val)
    hZ hN hM hMc hVc hzc hhc hIn hFn hRn hO hOM (by rw [hpow];exact hOn) hKlower
    (by linarith [divisorDyadicScale_ge_one i.val]) hKupper
    (by linarith [divisorDyadicScale_ge_one j.val]) hPupper hinv hmargin hVd hhd hd
    Rc Tc hTc hm hg hti hRi hGN hGchar
    (fun K hK => hrowcop K (divisorDyadicBin_subset rows Hrow i hK))
    (tuplePrimeFamily_product Tc hTc hm hg) hScop hSN hSchar
  let Dc : CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
      G rows hrows tuples hmax hgood Hrow Hslot i j := fun K p hp =>
    memberTupleControlled Tc hm hg G K.val (hRi K.val K.property) hTc hti (D K) p hp
  refine ⟨Dc,?_⟩
  intro θ r aw hr haw
  have hb := hD θ r aw (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val])
    (fun K hK => by convert hKr K hK using 1 ; ring_nf)
    (by
      intro P hP
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
      refine ⟨(hPnorm p (activeTupleDyad_subset tuples Hslot j hp)).1,?_⟩
      convert hPr p hp using 1 ; ring_nf)
    (fun K hK => hr K (divisorDyadicBin_subset rows Hrow i hK))
    (fun p hp => haw p (activeTupleDyad_subset tuples Hslot j hp))
  exact hb
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1663

/- Original source: OAI/NumberTheory/DirichletL/Reflection/InactiveBudget.lean; sha256: d8b62c103f04185104bfc64c9ff5ebb07bd6709a92ebd4f5344cb8adbf5cd806 -/
section Source1664
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section

lemma subtype_product_le_full {σ : Type*} [Fintype σ] (p : σ→Prop) [DecidablePred p]
    (H : σ→ℝ) (hH : ∀ i,1≤H i) :
    (∏ i : {i // p i},H i.val)≤∏ i,H i := by
  rw [←Finset.prod_subtype (Finset.univ.filter p) (by simp) H]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
    (fun i _ => (zero_le_one.trans (hH i))) (fun i _ _ => hH i)

theorem harmonic_product_small_power (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤rmax → (∀ i,1≤H i) →
      (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤C*(∏ i,H i)^ε := by
  let D := max 1 (256*(2+1/((ε/2)*Real.log 2)))
  have hD : 1≤D := le_max_left _ _
  refine ⟨D^(2*rmax),by positivity,?_⟩
  intro σ _ H hcard hH
  have hp : 0<∏ i,H i := Finset.prod_pos (fun i _ => lt_of_lt_of_le zero_lt_one (hH i))
  have he (i : σ) : 256*(columnDyadicLength (H i)+1:ℝ)≤D*(H i)^(ε/2) := by
    apply (mul_le_mul_of_nonneg_left (columnDyadicLength_small_power (ε/2) (by positivity) (H i) (hH i)) (by norm_num : (0:ℝ)≤256)).trans
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (zero_le_one.trans (hH i)) _)
  calc
    _ ≤ (∏ i,D*(H i)^(ε/2))^2 := by
      apply pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => by positivity))
      exact Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => he i)
    _ = D^(2*Fintype.card σ)*(∏ i,H i)^ε := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        Real.finsetProd_rpow Finset.univ H (fun i _ => zero_le_one.trans (hH i)),mul_pow,←pow_mul,
        ←Real.rpow_mul_natCast hp.le]
      congr 1
      · congr 1;omega
      · congr 1;norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (Nat.mul_le_mul_left 2 hcard)) (Real.rpow_nonneg hp.le _)

theorem inactive_product_small_power (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (T : Finset σ) (H : σ→ℝ),
      Fintype.card σ≤rmax → (∀ i,1≤H i) →
      (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2≤C*(∏ i,H i)^ε := by
  obtain ⟨C,hC,hb⟩ := harmonic_product_small_power rmax ε hε
  refine ⟨C,hC,?_⟩
  intro σ _ T H hcard hH
  apply (hb (fun i : {i // i∉T} => H i.val)
    ((Fintype.card_subtype_le _).trans hcard) (fun i => hH i.val)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i.val)))
    (subtype_product_le_full (fun i => i∉T) H hH) hε.le
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1664

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalAggregation.lean; sha256: 4fe4f8851e609bc42527e55e8a1654c9751dba68017cf4e24fee1c8b3632293a -/
section Source1665
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma bounded_row_multiplier_energy {κ : Type*} (rows : Finset κ) (r f : κ→ℂ)
    (hr : ∀ k∈rows,‖r k‖≤1) :
    (∑ k∈rows,‖r k*f k‖^2)≤∑ k∈rows,‖f k‖^2 := by
  apply Finset.sum_le_sum
  intro k hk
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hr k hk)

theorem original_frozen_source_energy {κ σ : Type*} [Fintype σ]
    (rows : Finset κ) {m f : Eis} (z : κ→Eis) (D : ∀ k,GoodMaskRowData m f (z k))
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : ∀ n,‖Ψ n‖≤1)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (J F Q₀ : Ideal Eis)
    (g : (Eis⧸Ideal.span {c})→Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀)→Finset σ→κ→ℂ)
    (E : ℝ) (hg : ∀ h A T,(∑ k∈rows,‖g h A T k‖^2)≤E) :
    (∑ k∈rows,‖thetaDerivativeScalar⁻¹*
      ∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc ((D k).fixedFactor Ψ Q) h*
        ∑ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀),
          frozenInactiveWeight J F (Ideal.span {m}*F) Q₀ A*∑ T : Finset σ,g h A T k‖^2)≤
    ‖thetaDerivativeScalar⁻¹‖^2*
      (Fintype.card ((Eis⧸Ideal.span {c})×(Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀)×Finset σ)):ℝ)^2*E := by
  let B := (Eis⧸Ideal.span {c})×(Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀)×Finset σ)
  let v := fun (b : B) k => (fixedThetaRowCoeff c hc ((D k).fixedFactor Ψ Q) b.1*
    frozenInactiveWeight J F (Ideal.span {m}*F) Q₀ b.2.1)*g b.1 b.2.1 b.2.2 k
  have hv (b : B) : (∑ k∈rows,‖v b k‖^2)≤E := by
    apply (bounded_row_multiplier_energy rows _ _ (fun k hk =>
      original_fourier_frozen_weight_norm (D k) Ψ Q hΨ c hc b.1 J F Q₀ b.2.1)).trans
    exact hg b.1 b.2.1 b.2.2
  have he := weighted_finite_row_energy_uniform (Finset.univ : Finset B) rows (fun _ => (1:ℂ)) v E (fun b hb => hv b)
  simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at he
  have hid (k : κ) : (∑ b : B,v b k)=
      ∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc ((D k).fixedFactor Ψ Q) h*
        ∑ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀),
          frozenInactiveWeight J F (Ideal.span {m}*F) Q₀ A*∑ T : Finset σ,g h A T k := by
    simp only [B,v,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  simp_rw [←hid]
  simp only [norm_mul,mul_pow,←Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq (by ring)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1665

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SourceCost.lean; sha256: ba8413a5b6db65c79db905b1b13d16036eaf27fe5849d381e7b88e4efc880706 -/
section Source1666
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma pool_subset_choices_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (J Q Q₀ : Ideal Eis),J≠0 → Q≠0 →
      (Fintype.card (Finset (FreeReflection.pool J Q Q₀)):ℝ)^2≤C*(Ideal.absNorm (J*Q):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := original_pool_choice_count ε hε
  refine ⟨C,hC,?_⟩
  intro J Q Q₀ hJ hQ
  apply le_trans _ (hb J Q Q₀ hJ hQ)
  simp only [Fintype.card_finset,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by norm_num) _) _

theorem original_source_cost {χ : Type*} [Fintype χ] (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤rmax → (∀ i,1≤H i) →
    ∀ (J Q Q₀ : Ideal Eis),J≠0 → Q≠0 →
      (Fintype.card (χ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)):ℝ)^2*
        (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤
      C*(Ideal.absNorm (J*Q):ℝ)^ε*(∏ i,H i)^ε := by
  obtain ⟨Cp,hCp,hp⟩ := pool_subset_choices_small_power ε hε
  obtain ⟨Ch,hCh,hh⟩ := harmonic_product_small_power rmax ε hε
  let C := ((Fintype.card χ:ℝ)^2+1)*(2:ℝ)^(2*rmax)*Cp*Ch
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro σ _ H hcard hH J Q Q₀ hJ hQ
  have hs : (Fintype.card (Finset σ):ℝ)^2≤(2:ℝ)^(2*rmax) := by
    simp only [Fintype.card_finset,Nat.cast_pow,Nat.cast_ofNat,←pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hcf : (Fintype.card χ:ℝ)^2≤(Fintype.card χ:ℝ)^2+1 := by linarith
  have hprod : 0≤(∏ i,H i)^ε := Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) _
  have hnp : 0≤(Ideal.absNorm (J*Q):ℝ)^ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ = (Fintype.card χ:ℝ)^2*(Fintype.card (Finset (FreeReflection.pool J Q Q₀)):ℝ)^2*
        (Fintype.card (Finset σ):ℝ)^2*(∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2 := by
      simp only [Fintype.card_prod,Nat.cast_mul,mul_pow];ring
    _ ≤ ((Fintype.card χ:ℝ)^2+1)*(Cp*(Ideal.absNorm (J*Q):ℝ)^ε)*
        (2:ℝ)^(2*rmax)*(Ch*(∏ i,H i)^ε) := by
      gcongr
      · exact hp J Q Q₀ hJ hQ
      · exact hh H hcard hH
    _ = _ := by dsimp [C];ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1666

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SourceBudget.lean; sha256: 7e8e129ddc6652bde1f39a879f924b1c17ec21f4dccb800b22359fa1454b284c -/
section Source1667
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem original_source_cost_budget {χ : Type*} [Fintype χ]
    (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤rmax → (∀ i,1≤H i) →
    ∀ (J Q Q₀ : Ideal Eis),J≠0 → Q≠0 → ∀ (Z Lpool Lslot loss : ℝ),1<Z →
      (Ideal.absNorm (J*Q):ℝ)≤Z^Lpool → (∏ i,H i)≤Z^Lslot → ε*(Lpool+Lslot)≤loss →
      (Fintype.card (χ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)):ℝ)^2*
        (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤C*Z^loss := by
  obtain ⟨C,hC,hb⟩ := original_source_cost (χ:=χ) rmax ε hε
  refine ⟨C,hC,?_⟩
  intro σ _ H hcard hH J Q Q₀ hJ hQ Z Lpool Lslot loss hZ hpool hslot hloss
  have hz : 0<Z := lt_trans zero_lt_one hZ
  apply (hb H hcard hH J Q Q₀ hJ hQ).trans
  calc
    _ ≤ C*(Z^Lpool)^ε*(Z^Lslot)^ε := by
      have hp := Real.rpow_le_rpow (Nat.cast_nonneg (Ideal.absNorm (J*Q))) hpool hε.le
      have hs := Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) hslot hε.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hs
        (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) _) (by positivity)
    _ = C*Z^(ε*(Lpool+Lslot)) := by
      rw [←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,mul_assoc,←Real.rpow_add hz]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hloss) hC.le
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1667

/- Original source: OAI/NumberTheory/DirichletL/Reflection/DyadBudget.lean; sha256: 432fa77b6f96339b5f6942a99c2b405772c5d16454ef1c8873168b789e22df3c -/
section Source1668
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section

lemma columnDyadicLength_mono_pos {A B : ℝ} (hA : 0<A) (hAB : A≤B) :
    columnDyadicLength A≤columnDyadicLength B := by
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right (Real.log_le_log hA hAB) (Real.log_nonneg (by norm_num))

theorem actual_dyad_count_budget (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ Z Hrow Hslot : ℝ,1≤Z → 0<Hrow → 0<Hslot →
      Hrow≤Z^L → Hslot≤Z^L →
      (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2≤C*Z^ε := by
  let a := ε/(3*(L+1))
  have ha : 0<a := div_pos hε (by positivity)
  let B := 2+1/(a*Real.log 2)
  have hB : 0<B := by dsimp only [B];have := Real.log_pos (by norm_num : (1:ℝ)<2);positivity
  refine ⟨B^3,by positivity,?_⟩
  intro Z Hrow Hslot hZ hR hS hRc hSc
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hnorm := Real.one_le_rpow hZ hL
  have hcount := columnDyadicLength_small_power a ha (Z^L) hnorm
  have hr : (columnDyadicLength Hrow+1:ℝ)≤B*(Z^L)^a := by
    have hle : (columnDyadicLength Hrow+1:ℝ)≤(columnDyadicLength (Z^L)+1:ℝ) := by
      exact_mod_cast Nat.add_le_add_right (columnDyadicLength_mono_pos hR hRc) 1
    exact hle.trans hcount
  have hs : (columnDyadicLength Hslot+1:ℝ)≤B*(Z^L)^a := by
    have hle : (columnDyadicLength Hslot+1:ℝ)≤(columnDyadicLength (Z^L)+1:ℝ) := by
      exact_mod_cast Nat.add_le_add_right (columnDyadicLength_mono_pos hS hSc) 1
    exact hle.trans hcount
  have hexp : L*a*3≤ε := by
    have he : a*(3*(L+1))=ε := by dsimp [a];field_simp
    have hh : 0≤a := ha.le
    nlinarith
  calc
    _ ≤ (B*(Z^L)^a)*(B*(Z^L)^a)^2 := by gcongr
    _ = B^3*((Z^L)^a)^3 := by ring
    _ = B^3*Z^(L*a*3) := by
      rw [←Real.rpow_mul hz.le]
      have he := Real.rpow_mul_natCast hz.le (L*a) 3
      norm_num only [Nat.cast_ofNat] at he
      rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1668

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ChoiceTransport.lean; sha256: cc70193c4fbdf86265d9c39d701193506a6a6e188c03a1f796328fff8e68e70d -/
section Source1669
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

def fixedTupleFamily (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P) (P : Ideal Eis) : PrimeFamily σ :=
  tuplePrimeFamily (fixedSlotTupleSet L F) hne
    (fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i))
    (fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)) P

lemma fixedTupleFamily_at_choice (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (p : ∀ i,L i) (hp : ∀ j i,(p i).val≠F j) :
    fixedTupleFamily L F hne hmax hgood (∏ i,(p i).val)=slotChoiceFamily L hmax hgood p := by
  apply PrimeFamily.eq_of_ideal_eq
  exact tuplePrimeFamily_at_product (fixedSlotTupleSet L F) hne _ _
    (fixedSlotTupleSet_product_injective L F hL hprime) (fun i => (p i).val)
    ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p i).property,hp⟩)

def fixedTupleCoefficient (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ) (p : σ→Ideal Eis) : ℂ :=
  if hp:∀ i,p i∈L i then ∏ i,w i ⟨p i,hp i⟩ else 0

omit [DecidableEq σ] in
lemma fixedTupleCoefficient_at (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ) (p : ∀ i,L i) :
    fixedTupleCoefficient L w (fun i => (p i).val)=∏ i,w i (p i) := by
  simp only [fixedTupleCoefficient,dite_eq_left (show ∀ i,(p i).val∈L i from fun i => (p i).property)]

omit [DecidableEq σ] in
lemma fixedTupleCoefficient_norm (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (p : σ→Ideal Eis) : ‖fixedTupleCoefficient L w p‖≤1 := by
  unfold fixedTupleCoefficient
  split
  · exact slot_coefficient_norm L w hw _
  · simp

variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily τ) (K : Ideal Eis) (hK : Admissible K)
    (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (D : ∀ P : (fixedSlotTupleSet L F).image slotTupleProduct,IsCoprime K P.val→
      ControlledStratumArithmetic (G.reflected K hK (fixedTupleFamily L F hne hmax hgood P.val)).generator N a c mode)
    (p : supportedSlotChoices L F K)

def activeChoiceControlled :
      ControlledStratumArithmetic (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator N a c mode :=
  castControlled (congrArg (fun S => (G.reflected K hK S).generator)
    (fixedTupleFamily_at_choice L F hne hmax hgood hL hprime p.val p.property.2))
    (D ⟨∏ i,(p.val i).val,Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩ p.property.1)

lemma activeChoiceControlled_value
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (activeChoiceControlled G K hK L F hne hmax hgood hL hprime D p) s
      (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
      (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
      (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) W X=
    mixedReflectedValue (D ⟨∏ i,(p.val i).val,Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩ p.property.1) s
      (G.reflected K hK (fixedTupleFamily L F hne hmax hgood (∏ i,(p.val i).val))).generator_ne_zero hc
      (G.reflected K hK (fixedTupleFamily L F hne hmax hgood (∏ i,(p.val i).val))).generator_good
      (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) W X := by
  exact mixedReflectedValue_cast _ _ s _ _ hc _ _ _ _ W X

theorem literalWholeRow_eq_original_choices
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : τ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (w : ∀ i,L i→ℂ) :
    literalWholeRow G K hK (fixedTupleFamily L F hne hmax hgood) j
      ((fixedSlotTupleSet L F).image slotTupleProduct) D s hc W θ X r
      (slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w))=
    ∑ p : supportedSlotChoices L F K,r K*(∏ i,w i (p.val i))*
      mixedReflectedValue (activeChoiceControlled G K hK L F hne hmax hgood hL hprime D p) s
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
        (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X := by
  let e := supportedSlotProductEquiv L F hL hprime K
  unfold literalWholeRow
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [activeChoiceControlled_value G K hK L F hne hmax hgood hL hprime D p s hc j]
  have hcft : slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w)
      (e p).val.val=∏ i,w i (p.val i) := by
    change slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w)
      (slotTupleProduct (fun i => (p.val i).val))=_
    rw [slotProductCoefficient_at_product (fixedSlotTupleSet L F)
      (fixedSlotTupleSet_product_injective L F hL hprime) (fixedTupleCoefficient L w)
      (fun i => (p.val i).val) ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩)]
    exact fixedTupleCoefficient_at L w p.val
  rw [hcft]
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1669

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MemberChoiceTransport.lean; sha256: a8b9e85db4f365531263c825c6ce4b2656f5d68b81360aac17bc0c6ce341185f -/
section Source1670
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
variable (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

abbrev originalTupleMax : ∀ p∈fixedSlotTupleSet L F,∀ i,(p i).IsMaximal :=
  fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)
abbrev originalTupleGood : ∀ p∈fixedSlotTupleSet L F,∀ i,ConcretePrimeRowBridge.goodLambda∉p i :=
  fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)

variable {N a c : Eis} {mode : Bool} (G : PrimeFamily τ) (K : Ideal Eis) (hK : Admissible K)
variable (D : ∀ p : fixedSlotTupleSet L F,IsCoprime K (slotTupleProduct p.val)→
    ControlledStratumArithmetic (G.reflected K hK
      (memberTupleFamily (fixedSlotTupleSet L F) (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator N a c mode)

def memberChoiceControlled (p : supportedSlotChoices L F K) :
    ControlledStratumArithmetic (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator N a c mode :=
  D ((supportedSlotTupleEquiv L F K) p).val ((supportedSlotTupleEquiv L F K) p).property

theorem member_source_eq_original_choices
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) (r : ℂ) (w : ∀ i,L i→ℂ) :
    (∑ p : fixedSlotTupleSet L F,if hp:IsCoprime K (slotTupleProduct p.val) then
      r*fixedTupleCoefficient L w p.val*mixedReflectedValue (D p hp) s
        (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
          (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_ne_zero hc
        (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
          (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X else 0)=
    ∑ p : supportedSlotChoices L F K,r*(∏ i,w i (p.val i))*
      mixedReflectedValue (memberChoiceControlled L F hmax hgood G K hK D p) s
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X := by
  let e := supportedSlotTupleEquiv L F K
  have he := sum_subtype_dite_decidable (fun p : fixedSlotTupleSet L F => IsCoprime K (slotTupleProduct p.val))
    (fun p hp => r*fixedTupleCoefficient L w p.val*mixedReflectedValue (D p hp) s
      (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
        (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_ne_zero hc
      (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
        (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X)
  rw [←he,←e.sum_comp]
  apply Finset.sum_congr rfl
  intro p hp
  change r*fixedTupleCoefficient L w (fun i => (p.val i).val)*_=_
  rw [fixedTupleCoefficient_at]
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1670

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CanonicalChoiceEnergy.lean; sha256: 50339ed6e48b0836ffe9290bfcbc850057786eb2df1cacf542d91400ecf6b7ab -/
section Source1671
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem canonical_original_choice_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (hB : B≠0) (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0) (_hR : R≠0),
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z N V M z₀ margin O₀ hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ K : rows,∀ p : supportedSlotChoices lists (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily lists hmax hgood p.val)).generator Nlevel (a g) (c₀ g) (mode g),
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ), (∀ i P,‖w i P‖≤1) →
      (∑ K : rows,‖∑ p : supportedSlotChoices lists (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
        (∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
          (reflectedExponent jF) (slotIndices A (PrimeIndex K.val) σ)
          (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_dyadic_geometry_uniform a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac B hB L cstar η hL hcstar hη hη1 hηc
  obtain ⟨Cb,hCb,hbins⟩ := actual_dyad_count_budget L (cstar/32) hL (by positivity)
  refine ⟨degree,Cb*C,Z₀,mul_pos hCb hC,hZ₀,?_⟩
  intro g σ _ _ J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents hsub hbad
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH hprod hGN hGchar hrowcop hLN hLchar
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let FF := (poolPrimeFamily J (B*F*R) Q₀).ideal
  let tuples := fixedSlotTupleSet lists FF
  let hm := originalTupleMax lists FF hmax
  let hg := originalTupleGood lists FF hgood
  have htuples : ∀ p∈tuples,∀ i,p i∈lists i := fun p hp => ((mem_fixedSlotTupleSet lists FF p).mp hp).1
  have hpair : ∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hm hg p)).ideal) := by
    intro p
    apply PrimeFamily.sum_pairwise G _ ((poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A)
    · intro i j hij
      apply Ideal.isCoprime_of_isMaximal
      intro heq
      change p.val i=p.val j at heq
      exact Finset.disjoint_left.mp (hdis hij) (htuples p.val p.property i)
        (heq.symm ▸ htuples p.val p.property j)
    · intro f i
      apply Ideal.isCoprime_of_isMaximal
      exact (((mem_fixedSlotTupleSet lists FF p.val).mp p.property).2 f.val i).symm
  have hPN : ∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (memberTupleFamily tuples hm hg p)).ideal b) := by
    intro p b
    cases b with
    | inl f => exact hGN f
    | inr i => exact hLN i _ (htuples p.val p.property i)
  have hPchar : ∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hm hg p)).ideal b)≠2 := by
    intro p b
    cases b with
    | inl f => exact hGchar f
    | inr i => exact hLchar i _ (htuples p.val p.property i)
  have hPnorm : ∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Z^z₀ := by
    intro p hp
    refine ⟨slotTupleProduct_admissible lists hdis hprime ?_ p (htuples p hp),?_⟩
    · intro i P hPi
      let : P.IsMaximal := hmax i P hPi
      exact (primaryPrime_eq_primaryGenerator P).symm ▸ primaryPrime_ne_zero P (hgood i P hPi)
    · exact (slotTupleProduct_norm_bound lists H (fun i P hPi => (hprime i P hPi).ne_zero) hH p (htuples p hp)).2.trans hprod
  let Hrow := Z^M/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J (B*F*R)):ℝ))
  let Hslot := Z^z₀
  obtain ⟨Dc,hDc⟩ := he g J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d
    hZ hN hM hMc hVc hzc hhc hFn hRn hO hOM hOn hinv hmargin hVd hhd hd
    parents rows hparents hsub hbad tuples hm hg (fixedSlotTupleSet_product_injective lists FF hdis hprime)
    hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let D := fun (K : rows) (p : supportedSlotChoices lists FF K.val) =>
    memberChoiceControlled lists FF hmax hgood G K.val (hrows K.val K.property)
      (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K) p
  refine ⟨D,?_⟩
  intro θ w hw
  have hsource (K : rows) :
      (∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc (s g) (hc₀ g)
        (fun b : A => completedLocalExponent J F b.val.val) W θ (Z^(N-3*hhat)) (fun _ => 1)
        (fixedTupleCoefficient lists w) K p)=
      ∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) := by
    simpa only [dyadicPhysicalTerm,D,one_mul] using member_source_eq_original_choices lists FF hmax hgood G K.val
      (hrows K.val K.property) (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K)
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) 1 w
  have hb := hDc θ (fun _ => 1) (fixedTupleCoefficient lists w) (by simp) (fun p hp => fixedTupleCoefficient_norm lists w hw p)
  have hid : (∑ K : rows,‖∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val) W θ (Z^(N-3*hhat))
      (fun _ => 1) (fixedTupleCoefficient lists w) K p‖^2)=
      ∑ K : rows,‖∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    exact congrArg (fun z : ℂ => ‖z‖^2) (hsource K)
  apply (hid.symm.trans_le hb).trans
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzpos : 0<Z := lt_trans zero_lt_one hz
  have hp : (1:ℝ)≤Ideal.absNorm (rowPowerfulPart J) := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
  have hm' : (1:ℝ)≤Ideal.absNorm (rowMaskPart J (B*F*R)) :=
    QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart J) (B*F*R))
  have hRpos : 0<Hrow := by dsimp [Hrow];positivity
  have hScap : Hslot≤Z^L := Real.rpow_le_rpow_of_exponent_le hz.le hzc
  have hRcap : Hrow≤Z^L := by
    exact (div_le_self (Real.rpow_nonneg hzpos.le _) (one_le_mul_of_one_le_of_one_le hp hm')).trans
      (Real.rpow_le_rpow_of_exponent_le hz.le hMc)
  have hcount := hbins Z Hrow Hslot hz.le hRpos (Real.rpow_pos_of_pos hzpos _) hRcap hScap
  calc
    _ ≤ (Cb*Z^(cstar/32))*(C*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O₀/2)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (Cb*C)*(1+‖θ‖)^degree*Z^(cstar/32+(N+V-3*cstar/16-O₀/2)) := by
      rw [Real.rpow_add hzpos];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1671

/- Original source: OAI/NumberTheory/DirichletL/Reflection/InactiveSource.lean; sha256: c6b2582c6276aa824c3a70762dcb7cd7e8a11cf2d826e72f90ca104e0d03e693 -/
section Source1672
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

lemma supported_inactive_sum_eq (rows : Finset (Ideal Eis))
    (L : σ→Finset (Ideal Eis)) (T : Finset σ) (F : φ→Ideal Eis)
    (K : rows) (w : ∀ i,L i→ℂ)
    (f : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val→ℂ) :
    (∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f b)=
    ∑ b : ∀ i : {i // i∉T},L i.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i)))*
        (if hk:K.val∈inactiveRowSet rows L T F b then f ⟨b,(Finset.mem_filter.mp hk).2⟩ else 0) := by
  let ok := fun b : ∀ i : {i // i∉T},L i.val =>
    IsCoprime K.val (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠F j
  let wt := fun b : ∀ i : {i // i∉T},L i.val =>
    (∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i))
  have he := sum_subtype_dite_decidable ok (fun b hb => wt b*f ⟨b,hb⟩)
  change (∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,wt b.val*f b)=_
  calc
    _ = ∑ b,if hb:ok b then wt b*f ⟨b,hb⟩ else 0 := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hc : ok b
      · have hk : K.val∈inactiveRowSet rows L T F b := Finset.mem_filter.mpr ⟨K.property,hc⟩
        simp only [dite_eq_left hc,dite_eq_left hk,wt]
      · have hk : K.val∉inactiveRowSet rows L T F b := fun h => hc (Finset.mem_filter.mp h).2
        simp only [dite_eq_right hc,dite_eq_right hk,mul_zero]

theorem supported_inactive_source_energy (rows : Finset (Ideal Eis))
    (L : σ→Finset (Ideal Eis)) (T : Finset σ) (F : φ→Ideal Eis) (H : σ→ℝ)
    (hzero : ∀ i,∀ P∈L i,P≠0) (hH : ∀ i,∀ P∈L i,(Ideal.absNorm P:ℝ)≤H i)
    (w : ∀ i,L i→ℂ) (hw : ∀ i P,‖w i P‖≤1)
    (f : ∀ K : rows,supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val→ℂ)
    (E : ℝ) (hE : 0≤E)
    (hf : ∀ b : ∀ i : {i // i∉T},L i.val,
      (∑ K : inactiveRowSet rows L T F b,
        ‖f ⟨K.val,(Finset.mem_filter.mp K.property).1⟩ ⟨b,(Finset.mem_filter.mp K.property).2⟩‖^2)≤E) :
    (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f K b‖^2)≤
    (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*E := by
  let g := fun (b : ∀ i : {i // i∉T},L i.val) (K : inactiveRowSet rows L T F b) =>
    f ⟨K.val,(Finset.mem_filter.mp K.property).1⟩ ⟨b,(Finset.mem_filter.mp K.property).2⟩
  have he := original_inactive_restricted_energy rows L T F H hzero hH w hw g E hE hf
  have hh : (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f K b‖^2)=
      ∑ K∈rows,‖∑ b : ∀ i : {i // i∉T},L i.val,
        ((∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i)))*
          (if hk:K∈inactiveRowSet rows L T F b then g b ⟨K,hk⟩ else 0)‖^2 := by
    rw [←Finset.sum_coe_sort rows]
    apply Finset.sum_congr rfl
    intro K hK
    rw [supported_inactive_sum_eq rows L T F K w (f K)]
  exact hh.trans_le he
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1672

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CanonicalInactiveEnergy.lean; sha256: 14e10baf53b6f186f3b11f10051093eda16b8662632e77f51ebd6d3a1a3cec06 -/
section Source1673
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

lemma inactiveRows_mem {σ φ : Type*} [Fintype σ] [DecidableEq σ]
    (rows : Finset (Ideal Eis)) (lists : σ→Finset (Ideal Eis)) (T : Finset σ)
    (FF : φ→Ideal Eis) (b : ∀ i : {i // i∉T},lists i.val) (K : Ideal Eis) :
    K∈inactiveRowSet rows lists T FF b ↔ K∈rows ∧
      IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠FF j := by
  exact Finset.mem_filter

theorem canonical_original_inactive_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (hB : B≠0) (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0) (_hR : R≠0),
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z N V M z₀ margin O₀ hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∀ T : Finset σ,
    ∃ D : ∀ K : rows,
      ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
      ∀ p : supportedSlotChoices (fun i : T => lists i.val) (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator
          Nlevel (a g) (c₀ g) (mode g),
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ), (∀ i P,‖w i P‖≤1) →
      (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val)
        (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
        ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
        ∑ p : supportedSlotChoices (fun i : T => lists i.val) (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
          (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero (hc₀ g)
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
          (reflectedExponent jF) (slotIndices A (PrimeIndex K.val) T)
          (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))‖^2)≤
        (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*
          (C*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O₀/2)) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_original_choice_energy a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac B hB L cstar η hL hcstar hη hη1 hηc
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro g σ _ _ J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents hsub hbad
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar T
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let FF := (poolPrimeFamily J (B*F*R) Q₀).ideal
  let rowsb := fun b : ∀ i : {i // i∉T},lists i.val => inactiveRowSet rows lists T FF b
  have hbsub (b : ∀ i : {i // i∉T},lists i.val) : rowsb b⊆rows := by
    intro K hK
    exact ((inactiveRows_mem rows lists T FF b K).mp hK).1
  have hbr (b : ∀ i : {i // i∉T},lists i.val) : ∀ K∈rowsb b,Admissible K := fun K hK => hrows K (hbsub b hK)
  have hdisT : Pairwise (fun i j : T => Disjoint (lists i.val) (lists j.val)) := by
    intro i j hij
    exact hdis (fun hv => hij (Subtype.ext hv))
  have hpT : (∏ i : T,H i.val)≤Z^z₀ := by
    rw [Finset.prod_coe_sort]
    apply le_trans _ hprod
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ T)
      (fun i _ => zero_le_one.trans (hH1 i)) (fun i _ _ => hH1 i)
  have hall := fun b : ∀ i : {i // i∉T},lists i.val =>
    he g J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d
      hZ hN hM hMc hVc hzc hhc hFn hRn hO hOM hOn hinv hmargin hVd hhd hd
      parents (rowsb b) hparents ((hbsub b).trans hsub) hbad
      (fun i : T => lists i.val) (fun i : T => H i.val) hdisT
      (fun i => hmax i.val) (fun i => hgood i.val) (fun i => hprime i.val) (hbr b)
      (fun i => hH i.val) hpT hGN hGchar (fun K hK => hrowcop K (hbsub b hK))
      (fun i => hLN i.val) (fun i => hLchar i.val)
  choose Db hDb using hall
  let D := fun (K : rows)
    (b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val)
    (p : supportedSlotChoices (fun i : T => lists i.val) FF K.val) =>
      Db b.val ⟨K.val,(inactiveRows_mem rows lists T FF b.val K.val).mpr ⟨K.property,b.property⟩⟩ p
  refine ⟨D,?_⟩
  intro θ w hw
  let f := fun (K : rows) (b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val) =>
    ∑ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
      (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
      (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero (hc₀ g)
      (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
      (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) T)
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  apply supported_inactive_source_energy rows lists T FF H (fun i P hP => (hprime i P hP).ne_zero)
    hH w hw f (C*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O₀/2)) (by positivity)
  intro b
  exact hDb b θ (fun i : T => w i.val) (fun i P => hw i.val P)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1673

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SourcePhysical.lean; sha256: 38a90282bc1184d5282c79d3a6796749ebe8e2740ea5596b4f40bcebbc81918d -/
section Source1674
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily τ) (FF : φ→Ideal Eis) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (lists : σ→Finset (Ideal Eis)) (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) (T : Finset σ)

abbrev OriginalSplitCompletion :=
    ∀ K : rows,∀ _b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val,
      ∀ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode

def originalInactivePhysical
    (D : OriginalSplitCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G FF rows hrows lists hmax hgood T)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) (K : rows) : ℂ :=
    ∑ b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
      ∑ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
        (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) s
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K.val) T) W X
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1674

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CanonicalFrozenEnergy.lean; sha256: aaa7a653efdb960c9454de5cafc82c2f4a12a7038ba56487871f8cb854ab9c4c -/
section Source1675
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem canonical_original_frozen_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (hB : B≠0) (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0) (_hR : R≠0),
    ∀ (Z N V M z₀ margin O₀ hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm J:ℝ)≤Z^M → (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
    Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) ((poolPrimeFamily J (B*F*R) Q₀).ideal f)) →
      (∀ f,ringChar (Eis⧸(poolPrimeFamily J (B*F*R) Q₀).ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J (B*F*R) Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ g : γ,∀ A : Finset (FreeReflection.pool J (B*F*R) Q₀),∀ T : Finset σ,
      OriginalSplitCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
        ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (poolPrimeFamily J (B*F*R) Q₀).ideal
        rows hrows lists hmax hgood T,
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ) (scalar : γ → rows → ℂ),
      (∀ i P,‖w i P‖≤1) → (∀ g K,‖scalar g K‖≤1) →
      (∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ g : γ,scalar g K*
        ∑ A : Finset (FreeReflection.pool J (B*F*R) Q₀),frozenInactiveWeight J F (B*F*R) Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical
            ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (poolPrimeFamily J (B*F*R) Q₀).ideal
            rows hrows lists hmax hgood T (D g A T) (s g) (hc₀ g)
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w K‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/16-O₀/2) := by
  obtain ⟨degree,C,Z₁,hC,hZ₁,he⟩ := canonical_original_inactive_energy a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac B hB L cstar η hL hcstar hη hη1 hηc
  let ε := cstar/(32*(4*L+2))
  have hε : 0<ε := div_pos hcstar (by positivity)
  obtain ⟨Cb,hCb,hcost⟩ := original_source_cost_budget (χ:=γ) rmax ε hε
  let Z₀ := max Z₁ (Ideal.absNorm B:ℝ)
  refine ⟨degree,(‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C,Z₀,by positivity,hZ₁.trans_le (le_max_left _ _),?_⟩
  intro σ _ _ J F R Q₀ hJ hF hR Z N V M z₀ margin O₀ hhat d hZ hN hM hMc hVc hzc hhc
    hJn hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents hsub hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar
  have hz1 : Z₁≤Z := (le_max_left _ _).trans hZ
  have hz : 1<Z := lt_of_lt_of_le hZ₁ hz1
  have hzp : 0<Z := lt_trans zero_lt_one hz
  let FF := (poolPrimeFamily J (B*F*R) Q₀).ideal
  have hall := fun (g : γ) (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (T : Finset σ) =>
    he g J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d
      hz1 hN hM hMc hVc hzc hhc hFn hRn hO hOM hOn hinv hmargin hVd hhd hd
      parents rows hparents hsub hbad lists H hdis hmax hgood hprime hrows hH1 hH hprod
      (fun f => hGN f.val) (fun f => hGchar f.val)
      (fun K hK => ⟨fun f => (hrowcop K hK).1 f.val,(hrowcop K hK).2⟩) hLN hLchar T
  choose D hD using hall
  refine ⟨D,?_⟩
  intro θ w scalar hw hscalar
  let energy := C*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O₀/2)
  let harm := (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2
  let source := fun (g : γ) (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (T : Finset σ) (K : rows) =>
    originalInactivePhysical ((poolPrimeFamily J (B*F*R) Q₀).restrict A) FF rows hrows lists hmax hgood T
      (D g A T) (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w K
  have hs (g : γ) (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (T : Finset σ) :
      (∑ K : rows,‖source g A T K‖^2)≤harm*energy := by
    apply (hD g A T θ w hw).trans
    apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact subtype_product_le_full (fun i => i∉T) (fun i => 256*(columnDyadicLength (H i)+1:ℝ)) (fun i => by have hn : (0:ℝ)≤columnDyadicLength (H i) := Nat.cast_nonneg _; linarith)
  let Labels := γ×(Finset (FreeReflection.pool J (B*F*R) Q₀)×Finset σ)
  let f := fun (b : Labels) (K : rows) => (scalar b.1 K*frozenInactiveWeight J F (B*F*R) Q₀ b.2.1)*source b.1 b.2.1 b.2.2 K
  have hf (b : Labels) : (∑ K : rows,‖f b K‖^2)≤harm*energy := by
    apply (bounded_row_multiplier_energy Finset.univ _ _ (fun K hK => ?_)).trans (hs b.1 b.2.1 b.2.2)
    rw [norm_mul]
    exact (mul_le_mul (hscalar b.1 K) (frozenInactiveWeight_norm J F (B*F*R) Q₀ b.2.1)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hfam := weighted_finite_row_energy_uniform (Finset.univ : Finset Labels) (Finset.univ : Finset rows)
    (fun _ => (1:ℂ)) f (harm*energy) (fun b _ => hf b)
  simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hfam
  have hid (K : rows) : (∑ b : Labels,f b K)=∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J (B*F*R) Q₀),frozenInactiveWeight J F (B*F*R) Q₀ A*
        ∑ T : Finset σ,source g A T K := by
    simp only [Labels,f,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  have hsource : (∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J (B*F*R) Q₀),frozenInactiveWeight J F (B*F*R) Q₀ A*
        ∑ T : Finset σ,source g A T K‖^2)≤
      ‖thetaDerivativeScalar⁻¹‖^2*(Fintype.card Labels:ℝ)^2*harm*energy := by
    simp_rw [←hid]
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hfam (sq_nonneg _)).trans_eq (by ring)
  apply hsource.trans
  have hBn : (Ideal.absNorm B:ℝ)≤Z := (le_max_right _ _).trans hZ
  have hmaskn := canonical_mask_norm_cap B F R Z V L L hz.le hBn hFn hRn hVc (le_refl _)
  have hJn' : (Ideal.absNorm J:ℝ)≤Z^L := hJn.trans (Real.rpow_le_rpow_of_exponent_le hz.le hMc)
  have hpool : (Ideal.absNorm (J*(B*F*R)):ℝ)≤Z^(3*L+1) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _ ≤ Z^L*Z^(2*L+1) := mul_le_mul hJn' hmaskn (Nat.cast_nonneg _) (Real.rpow_nonneg hzp.le _)
      _ = _ := by rw [←Real.rpow_add hzp];congr 1;ring
  have hbudget : ε*((3*L+1)+L)≤cstar/32 := by
    have heq : ε*(4*L+2)=cstar/32 := by dsimp [ε];field_simp
    have hh := mul_le_mul_of_nonneg_left (show (3*L+1)+L≤4*L+2 by linarith) hε.le
    rwa [heq] at hh
  have hcst := hcost H hcard hH1 J (B*F*R) Q₀ hJ (mul_ne_zero (mul_ne_zero hB hF) hR)
    Z (3*L+1) L (cstar/32) hz hpool
    (hprod.trans (Real.rpow_le_rpow_of_exponent_le hz.le hzc)) hbudget
  calc
    _ = ‖thetaDerivativeScalar⁻¹‖^2*((Fintype.card Labels:ℝ)^2*harm)*energy := by ring
    _ ≤ (‖thetaDerivativeScalar⁻¹‖^2+1)*(Cb*Z^(cstar/32))*energy := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
      exact mul_le_mul (by linarith) hcst (by dsimp [harm];positivity) (by positivity)
    _ = ((‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C)*(1+‖θ‖)^degree*
        Z^(cstar/32+(N+V-cstar/8-O₀/2)) := by
      dsimp only [energy]
      rw [Real.rpow_add hzp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1675

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalSlotSupport.lean; sha256: c5661139f81ef3d6d08e156a23eb349d8d3f9ed04602cedfeb537f9ab87e13f5 -/
section Source1676
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

abbrev originalSlotChoices :=
  {p : ∀ i,L i // ∀ P : FreePrimeIndex D.movingIdeal Q₀,∀ i,(p i).val≠P.val.val}

def originalSlotSupportEquiv :
    originalSlotChoices D Q₀ L ≃ supportedSlotChoices L ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) where
  toFun p := ⟨p.val,(original_slot_mask_iff D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    (slotChoiceFamily L hmax hgood p.val)).mp p.property⟩
  invFun p := ⟨p.val,(original_slot_mask_iff D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    (slotChoiceFamily L hmax hgood p.val)).mpr p.property⟩
  left_inv _p := rfl
  right_inv _p := rfl

def originalSlotSplit (T : Finset σ) : originalSlotChoices D Q₀ L ≃
    supportedSlotChoices (fun i : {i // i∉T} => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) ×
      supportedSlotChoices (fun i : T => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) :=
  (originalSlotSupportEquiv D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood).trans
    (supportedSlotSplit L T ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)))

lemma originalSlotSplit_symm_val (T : Finset σ)
    (b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)))
    (a : supportedSlotChoices (fun i : T => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F))) :
    ((originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)).val=
      (slotChoiceSplit L T).symm (a.val,b.val) := rfl

theorem original_supported_slot_sum (T : Finset σ)
    (w : ∀ i,L i→ℂ) (H : originalSlotChoices D Q₀ L→ℂ) :
    (∑ p : originalSlotChoices D Q₀ L,
      (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p.val i).val:ℂ)⁻¹)*
        (∏ i,w i (p.val i))*H p)=
    ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
      ∑ a : supportedSlotChoices (fun i : T => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
        (∏ i : T,w i.val (a.val i))*
        H ((originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)) := by
  rw [←(originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [originalSlotSplit_symm_val,slot_choice_inactive_weight,Equiv.apply_symm_apply,slot_coefficient_split]
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1676

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalSplitReflection.lean; sha256: f2f5ab334fc503bc8c3475301fa11a6af32536a31edfedab510f673be0b8bf8c -/
section Source1677
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

theorem actual_marked_slot_split_reflection
    (hS : ∀ p : ∀ i,L i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily L hmax hgood p).ideal))
    (hSodd : ∀ p : ∀ i,L i,∀ i,ringChar (Eis⧸(slotChoiceFamily L hmax hgood p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p : ∀ i,L i,∀ i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (slotChoiceFamily L hmax hgood p) Q).ideal i))
    (C : ∀ p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L,
      ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : ∀ i,L i→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (slotChoiceFamily L hmax hgood p).ideal i∣A then (1:ℂ) else 0))=
    let physical := fun (h : Eis⧸Ideal.span {c})
      (A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})))
      (T : Finset σ) (p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L) =>
      mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ T : Finset σ,
          ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
            ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
            (rowResidualPart I (Ideal.span {m}*F)),
            ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
              ∑ a : supportedSlotChoices (fun i : T => L i.val)
                ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
                (rowResidualPart I (Ideal.span {m}*F)),
                (∏ i : T,w i.val (a.val i))*physical h A T
                  ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)) := by
  dsimp only
  rw [actual_marked_tuple_reflection D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    (fun p : ∀ i,L i => slotChoiceFamily L hmax hgood p) hS hSodd Ψ hΨnorm hQ hΨperiod hmLam hm2
    c hc hcQ G N hN hNp C (fun p => ∏ i,w i (p i)) W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  have hs :=
    (original_supported_slot_sum D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
      L hmax hgood T w (fun p => mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X))
  convert hs using 1
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  congr 1
  apply Finset.prod_congr (by ext; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro t ht
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1677

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalChoiceControl.lean; sha256: a3d7751b87971184d09f917165cabff681f9f2fcfca9d670ddfa28bdb3ad1bc7 -/
section Source1678
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

lemma originalSplit_active_family (T : Finset σ) (p : originalSlotChoices D Q₀ L) :
    (slotChoiceFamily L hmax hgood p.val).restrict T=
      slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val)
        ((originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).2.val) := by
  let e := originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T
  calc
    _ = (slotChoiceFamily L hmax hgood (e.symm (e p)).val).restrict T :=
      congrArg (fun q : originalSlotChoices D Q₀ L => (slotChoiceFamily L hmax hgood q.val).restrict T) (e.symm_apply_apply p).symm
    _ = _ := by
      rw [originalSlotSplit_symm_val,slotChoiceFamily_active]

variable {τ : Type*} [Fintype τ] (Frozen : PrimeFamily τ) {N a c : Eis} {mode : Bool}
variable (T : Finset σ)
    (C : ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
        (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode)

def originalSplitControlled (p : originalSlotChoices D Q₀ L) :
    ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
      (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
      ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator N a c mode :=
  castControlled (congrArg (fun S => (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
    (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) S).generator)
    (originalSplit_active_family D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).symm)
    (C (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).1
      (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).2)

lemma originalSplitControlled_value (p : originalSlotChoices D Q₀ L)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue
      (originalSplitControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood Frozen T C p) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X=
    let q := originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p
    mixedReflectedValue (C q.1 q.2) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X := by
  exact mixedReflectedValue_cast _ _ s _ _ hc _ _ _ _ W X

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1678

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalChoicePhysical.lean; sha256: 1d0454ee6f7945d02d6bf009e7b71943e23f474f1f50e148fd45a67fa2a2ccd9 -/
section Source1679
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

variable {τ : Type*} [Fintype τ] (Frozen : PrimeFamily τ) {N a c : Eis} {mode : Bool}
variable (T : Finset σ)
    (C : ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
        (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode)

def originalSplitPhysical
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ)
    (q : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
      ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) ×
      supportedSlotChoices (fun i : T => L i.val)
      ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F))) : ℂ :=
  mixedReflectedValue (C q.1 q.2) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X
lemma originalSplitControlled_physical (p : originalSlotChoices D Q₀ L)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue
      (originalSplitControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood Frozen T C p) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X=
    originalSplitPhysical R I F Q₀ hbad L hmax hgood Frozen T C s hc jF W X
      (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p) := by
  exact originalSplitControlled_value D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    L hmax hgood Frozen T C p s hc jF W X

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1679
