import Analysis.MeasureTheory.Section_1_4_3

/-!
# Introduction to Measure Theory, Section 1.4.4: Measurable functions, and integration on a measure space

A companion to (the introduction to) Section 1.4.4 of the book "An introduction to Measure Theory".

import Analysis.MeasureTheory.Section_1_4_3

open Set MeasureTheory Function

/-! 
# Section 1.4.4: Measurable functions
Formalizing the interface for measurable functions to ensure build stability.
-/

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- The composition of measurable functions is measurable. -/
theorem Measurable.comp {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) : 
  Measurable (g ∘ f) := 
sorry

/-- The supremum of measurable functions is measurable. -/
theorem measurable_supr_ereal {f : ℕ → α → EReal} (hf : ∀ n, Measurable (f n)) : 
  Measurable (fun x => ⨆ n, f n x) := 
sorry
