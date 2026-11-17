import ProfReg.ChangeOfBase
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic

-- ============================================================
-- P2  -  CB₃ : V₁ → V₃, portée exacte du candidat identité
-- V₁ = ([0,1], min, 1), ordre <=  (orientation actée le
--   6 septembre 2026 ; voir BaseCategories.lean et NT-ARCH §2ter)
-- V₃ = (ℝ comme ℝ-module, ×, 1)  -  candidat minimal
-- ============================================================

-- Candidat naturel : φ(f) = f
--
-- Sous l'ordre <= de V₁ — contraint par la contravariance de CB₂ —
-- la condition de LAX monoïdalité s'écrit φ(a)·φ(b) → φ(min a b),
-- c'est-à-dire  a * b <= min a b.  Elle est VRAIE sur [0,1] :
-- le candidat identité EST lax monoïdal.
--
-- Ce qui est réfuté ci-dessous est la condition OPLAX,
-- soit l'inégalité inverse  min a b <= a * b.
--
-- [CORRECTION — 6 septembre 2026, porteur : Pierre Musseau]
-- Ce théorème s'appelait CB3_candidate_not_lax_monoidal.
-- Sa preuve est inchangée ; seule sa dénomination portait
-- au-delà de ce qu'il établit. L'obligation de déclarer
-- fractionactorielle ne repose pas sur lui, mais sur l'invariant
-- de typage et sur la LACUNE DÉCLARÉE portant sur l'inexistence
-- GÉNÉRALE d'un foncteur de calcul V₁→V₃
-- (correction C1, note de bilan ProfReg du 11 juin 2026).

-- THÉORÈME : le candidat identité n'est PAS oplax monoïdal
theorem CB3_candidate_not_oplax_monoidal :
    ¬ ∀ (a b : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      min a b ≤ a * b := by
  -- contre-exemple : a = 1/2, b = 1/2
  -- min(1/2, 1/2) = 1/2 > 1/4 = (1/2)*(1/2)
  intro h
  have := h (1/2) (1/2) (by norm_num) (by norm_num)
                         (by norm_num) (by norm_num)
  norm_num at this
