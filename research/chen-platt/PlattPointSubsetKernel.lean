import PlattGlobalGridKernel

namespace ChenEffective.PlattWindow

/-- Composable point-stream containment. Closed arithmetic checks are confined
to small leaves; concatenation transports them without one huge reduction. -/
inductive PointSubset : List PrimePoint → List PrimePoint → Prop
  | refl (xs : List PrimePoint) : PointSubset xs xs
  | left (xs ys : List PrimePoint) : PointSubset xs (xs++ys)
  | right (xs ys : List PrimePoint) : PointSubset ys (xs++ys)
  | trans {xs ys zs : List PrimePoint} :
      PointSubset xs ys → PointSubset ys zs → PointSubset xs zs
  | append {xs ys zs : List PrimePoint} :
      PointSubset xs zs → PointSubset ys zs → PointSubset (xs++ys) zs
  | checked {fuel : Nat} {xs ys : List PrimePoint} :
      checkPointCoverAux fuel ys xs=true → PointSubset xs ys

theorem pointSubset_aux_sound {fuel : Nat} {xs ys : List PrimePoint}
    (h : checkPointCoverAux fuel xs ys=true) : ∀p∈ys,p∈xs := by
  induction fuel generalizing xs ys with
  | zero =>
    cases ys with
    | nil => simp
    | cons q qs => simp [checkPointCoverAux] at h
  | succ n ih =>
    cases ys with
    | nil => simp
    | cons q qs =>
      cases xs with
      | nil => simp [checkPointCoverAux] at h
      | cons p ps =>
        simp only [checkPointCoverAux] at h
        split at h
        next he =>
          intro v hv
          cases List.mem_cons.mp hv with
          | inl heq =>
            simpa only [heq,he] using (List.mem_cons_self : p∈p::ps)
          | inr hv => exact ih h v hv
        next _ =>
          intro v hv
          exact List.mem_cons_of_mem p (ih h v hv)

theorem PointSubset.sound {xs ys : List PrimePoint} (h : PointSubset xs ys) :
    ∀p∈xs,p∈ys := by
  induction h with
  | refl xs => intro p hp; exact hp
  | left xs ys => intro p hp; exact List.mem_append_left ys hp
  | right xs ys => intro p hp; exact List.mem_append_right xs hp
  | trans hxy hyz ihxy ihyz => intro p hp; exact ihyz p (ihxy p hp)
  | append hx hy ihx ihy =>
    intro p hp
    cases List.mem_append.mp hp with
    | inl hp => exact ihx p hp
    | inr hp => exact ihy p hp
  | checked h => exact pointSubset_aux_sound h

#print axioms PointSubset.sound
end ChenEffective.PlattWindow
