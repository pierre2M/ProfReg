-- ============================================================
-- ORIENTATION DES CATÉGORIES DE BASE
-- Acté le 6 septembre 2026. Porteur : Pierre Musseau.
-- Source : Annexe G (MRC v5), §I.2-I.3 et §III.2.
-- Versé au set : NT-ARCH §2ter (primitives de Couche 0).
--
-- V_att (= V2) : ordre >=  — convention de coût.
--   T (top) = exigence insatisfaisable -> R-INTERDIT-ABSOLU.
--   Déclaré en Annexe G §I.2 : « >= est l'ordre de V_att ».
--
-- V1 (= V_met) : ordre <=  — CONTRAINT, non choisi.
--   CB2 = -log renverse l'ordre : source et cible sont opposées.
--   Confirmé indépendamment par CB1 (false |-> 0, true |-> 1),
--   qui exige 0 -> 1 dans V1.
--
-- V0 : ordre usuel false <= true.
--
-- PORTÉE DE CB3 (voir CB3Attempt.lean) : sous l'ordre <= sur V1,
--   le candidat identité phi(f) = f vers (R, x, 1) EST lax monoïdal
--   (a*b <= min(a,b) est vraie sur [0,1]). Le théorème de CB3Attempt
--   réfute la condition OPLAX. Aucune compilation ne distingue les
--   deux cas : c'est une déclaration, pas une vérification.
--
-- LACUNE OUVERTE — produit monoïdal de V2.
--   Annexe G §III.2 déclare une métrique de Lawvere, dont le produit
--   est l'addition (unité 0). Or CB2 transporte min en max :
--   -log(min(a,b)) = max(-log a, -log b). Le produit induit est donc
--   max (ultramétrique), non +. [INCOHÉRENCE INTER-COUCHES — niveau 0]
--   Conditionne l'agrégation des dettes, donc le nœud D
--   (commutativité micro-macro). [À TRANCHER PAR LE PORTEUR — v6]
-- ============================================================

import Mathlib.Data.Real.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Data.ENNReal.Basic

-- V₀ : booléen
-- Rien à définir, Bool est dans Lean 4 core
#check Bool

-- V₁ : intervalle [0,1]
#check unitInterval          -- Set.Icc (0:ℝ) 1
#check Set.Icc (0:ℝ) 1

-- V₂ : ℝ≥0∞ (réels étendus non-négatifs, inclut +∞)
#check ENNReal               -- c'est ℝ≥0 ∪ {+∞}
#check (⊤ : ENNReal)         -- +∞
#check (0 : ENNReal)
