import Mathlib.Tactic

/-!
# Analysis I, Appendix A.3: The structure of proofs

Some examples of proofs

-/

/-- Proposition A.3.1 -/
example {A B C D: Prop} (hAC: A → C) (hCD: C → D) (hDB: D → B): A → B := by
  intro h
  apply hAC at h
  apply hCD at h
  apply hDB at h
  exact h

/-- Proposition A.3.2 -/
example {x:ℝ} : x = Real.pi → Real.sin (x/2) + 1 = 2 := by
  intro h
  -- congr() produces an equality (or similar relation) from one or more existing relations, such as `h`, by substituting that relation in every location marked with a `$` sign followed by that relation, for instance `h` would be substituted at every location of `$h`.
  replace h := congr($h/2)
  replace h := congr(Real.sin $h)
  simp at h
  replace h := congr($h + 1)
  convert h
  norm_num


/-- Proposition A.3.1, alternate proof -/
example {A B C D: Prop} (hAC: A → C) (hCD: C → D) (hDB: D → B): A → B := by
  intro h
  suffices hD : D
  . exact hDB hD
  suffices hC : C
  . exact hCD hC
  exact hAC h

/-- Proposition A.3.2, alternate proof -/
example {x:ℝ} : x = Real.pi → Real.sin (x/2) + 1 = 2 := by
  intro h
  suffices h1 : Real.sin (x/2) = 1
  . simp [h1]
    norm_num
  suffices h2 : x/2 = Real.pi/2
  . simp [h2]
  simp [h]

/-- Proposition A.3.3 -/
example {r:ℝ} (h: 0 < r) (h': r < 1) : Summable (fun n:ℕ ↦ n * r^n) := by
  apply summable_of_ratio_test_tendsto_lt_one h' _ _
  . simp [Filter.eventually_atTop]
    use 1
    intro b hb
    simp [show b ≠ 0 by linarith, show r ≠ 0 by linarith]
  suffices hconv: Filter.atTop.Tendsto (fun n:ℕ ↦ r * ((n+1) / n)) (nhds r)
  . apply hconv.congr'
    simp [Filter.EventuallyEq, Filter.eventually_atTop]
    use 1
    intro b hb
    have : b > 0 := by linarith
    have hb1 : (b+1:ℝ) > 0 := by linarith
    simp [abs_of_pos h, abs_of_pos hb1]
    field_simp
    ring_nf
  suffices hconv : Filter.atTop.Tendsto (fun n:ℕ ↦ ((n+1:ℝ) / n)) (nhds 1)
  . convert hconv.const_mul r
    simp
  suffices hconv : Filter.atTop.Tendsto (fun n:ℕ ↦ 1 + 1/(n:ℝ)) (nhds 1)
  . apply hconv.congr'
    simp [Filter.EventuallyEq, Filter.eventually_atTop]
    use 1
    intro b hb
    have : (b:ℝ) > 0 := by norm_cast
    field_simp
  suffices hconv : Filter.atTop.Tendsto (fun n:ℕ ↦ 1/(n:ℝ)) (nhds 0)
  . convert hconv.const_add 1
    simp
  exact tendsto_one_div_atTop_nhds_zero_nat

/-- Proposition A.3.1, third proof -/
example {A B C D: Prop} (hAC: A → C) (hCD: C → D) (hDB: D → B): A → B := by
  intro h
  suffices hD : D
  . exact hDB hD
  have hC : C := hAC h
  exact hCD hC

/-- Proposition A.3.4 -/
example {A B C D E F G H I:Prop} (hAE: A → E) (hEB: E ∧ B → F) (hADG : A → G → D) (hHI: H ∨ I) (hFHC : F ∧ H → C) (hAHG : A ∧ H → G) (hIG: I → G) (hIGC: G → C) : A ∧ B → C ∧ D := by
  intro ⟨ hA, hB ⟩
  have hE : E := hAE hA
  have hF : F := hEB ⟨hE, hB⟩
  suffices hCG : C ∧ G
  . obtain ⟨ hC, hG ⟩ := hCG
    have hD : D := hADG hA hG
    exact ⟨hC, hD⟩
  obtain hH | hI := hHI
  . have hC := hFHC ⟨ hF, hH⟩
    have hG := hAHG ⟨hA, hH⟩
    exact ⟨hC, hG⟩
  have hG := hIG hI
  have hC := hIGC hG
  exact ⟨hC, hG⟩

/-- Proposition A.3.5 -/
example {A B C D:Prop} (hBC: B → C) (hAD: A → D) (hCD: D → ¬ C) : A → ¬ B := by
  intro hA
  by_contra hB
  have hC : C := hBC hB
  have hD : D := hAD hA
  have hC' : ¬ C := hCD hD
  contradiction
