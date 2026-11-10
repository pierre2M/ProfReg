import ProfReg.Interactions
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic        -- fournit ENNReal, ⊤, ofReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic  -- fournit Real.log

-- ============================================================
-- CB₁ : V₀ → V₁  (booléen → flou)
-- ============================================================

def CB1 (b : Bool) : ℝ :=
  if b then (1 : ℝ) else (0 : ℝ)

theorem CB1_in_unit (b : Bool) : 0 ≤ CB1 b ∧ CB1 b ≤ 1 := by
  cases b <;> simp [CB1]

theorem CB1_lax_monoidal (a b : Bool) :
    CB1 (a && b) = min (CB1 a) (CB1 b) := by
  cases a <;> cases b <;> simp [CB1]

-- ============================================================
-- CB₂ : V₁ → V₂  (flou → métrique Lawvere via -log)
-- ============================================================

noncomputable def CB2 (f : ℝ) : ENNReal :=
  if f ≤ 0 then ⊤
  else ENNReal.ofReal (-Real.log f)

theorem CB2_one : CB2 1 = 0 := by
  simp [CB2, Real.log_one]

theorem CB2_zero : CB2 0 = ⊤ := by
  simp [CB2]
