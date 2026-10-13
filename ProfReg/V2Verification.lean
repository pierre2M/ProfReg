import ProfReg.ChangeOfBase
import Mathlib.Data.Real.Basic

def CompatibleExtension
    (p0 : Actor → Actor → Bool)
    (p1 : Actor → Actor → ℝ) : Prop :=
  ∀ a b : Actor, p1 a b = 1 ↔ p0 a b = true

theorem R1_preserved_under_CB1
    (p0 : Actor → Actor → Bool)
    (p1 : Actor → Actor → ℝ)
    (h_compat : CompatibleExtension p0 p1)
    (h_R1 : ∀ a b : Actor, p0 a b = true → p0 b a = true) :
    ∀ a b : Actor, p1 a b = 1 → p1 b a = 1 := by
  intro a b h_p1ab
  exact (h_compat b a).mpr (h_R1 a b ((h_compat a b).mp h_p1ab))

-- ============================================================
-- RÉSULTAT DE SYNTHÈSE V2
-- ============================================================

-- Rappel du résultat sur le régime SYSTEMIQUE (prouvé dans Interactions.lean)
#check systemique_sans_creancier_viole_R1

-- Les deux résultats de P1 :
-- 1. R1_preserved_under_CB1 : Issue A — R1 préservé par CB₁ sous condition
-- 2. systemique_sans_creancier_viole_R1 : Issue B — tension T3 formellement établie
