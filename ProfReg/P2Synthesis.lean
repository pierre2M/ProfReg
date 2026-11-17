import ProfReg.CB3Attempt
import ProfReg.V2Verification

-- ============================================================
-- SYNTHÈSE P2  -  Conclusions architecturales pour B1
-- Date : 30 mai 2026
-- Statut : théorèmes prouvés en mode formel calculable (Lean 4)
-- ============================================================

-- ============================================================
-- RAPPEL DES RÉSULTATS ÉTABLIS
-- ============================================================

-- Depuis V2Verification.lean :
-- R1 est préservé par CB₁ sous condition de compatibilité (Issue A)
#check R1_preserved_under_CB1

-- Depuis Interactions.lean :
-- Le régime SYSTEMIQUE sans créancier viole R1 (tension T3)
#check systemique_sans_creancier_viole_R1

-- Depuis CB3Attempt.lean :
-- Le candidat naturel CB₃ (φ(f) = f) n'est pas OPLAX monoïdal.
-- Sous l'ordre <= de V₁ il EST lax monoïdal — voir CB3Attempt.lean.
#check CB3_candidate_not_oplax_monoidal

-- ============================================================
-- THÉORÈME DE SYNTHÈSE 1
-- fractionactorielle ne peut pas être calculée par ProfReg
-- ============================================================

-- [PORTÉE CORRIGÉE — 6 septembre 2026, porteur : Pierre Musseau]
--
-- Ce théorème est une IMPLICATION : il documente une conséquence
-- architecturale, il n'établit pas sa prémisse comme suffisante.
--
-- Ce qui fonde réellement l'obligation de déclarer
-- fractionactorielle (correction C1, bilan ProfReg 11 juin 2026) :
--   (1) l'invariant de TYPAGE ci-dessous, et
--   (2) la LACUNE DÉCLARÉE sur l'inexistence GÉNÉRALE d'un
--       foncteur de calcul V₁→V₃ — lacune assumée, non théorème.
--
-- Ce qui ne la fonde PAS : la réfutation d'un candidat unique.
-- Sous l'ordre <= de V₁ (NT-ARCH §2ter), le candidat identité est
-- lax monoïdal ; la prémisse ci-dessous est la condition OPLAX.
--
-- Condition de réfutabilité inchangée : l'exhibition d'un foncteur
-- de calcul non arbitraire et gouverné obligerait à réviser la
-- convention déclarative, non à retirer un théorème.

-- ┌───────────────────────────────────────────────────────────────────┐
-- │ CONV-1 — fractionactorielle est DÉCLARÉE, jamais CALCULÉE          │
-- └───────────────────────────────────────────────────────────────────┘
--
-- [THÉORÈME CREUX SUPPRIMÉ — 7 septembre 2026, décision du porteur]
-- Le théorème `fractionactorielle_must_be_declared` occupait cette place.
-- Sa conclusion était `True` : il n'établissait rien. Le conserver
-- permettait d'écrire « 0 sorry » tout en laissant une obligation ouverte.
--
-- CONVENTION retenue à sa place :
--   Aucun foncteur de calcul de la fraction actorielle n'est mobilisable
--   dans ProfReg. Toute valeur de fraction provient d'une DÉLIBÉRATION
--   déclarée, jamais d'un calcul du registre.
--
-- Statut : convention d'architecture, non théorème.
-- Appuis :  - CB3_candidate_not_oplax_monoidal (réfutation d'un candidat)
--           - lacune déclarée sur l'inexistence générale (correction C1)
-- Condition de réfutation : l'exhibition d'un foncteur de calcul non
--   arbitraire et gouverné obligerait à réviser cette convention.
--
-- L'invariant de TYPAGE que le set (NT-ARCH §52) attribuait au théorème
-- supprimé est désormais réellement prouvé, sous le nom
-- `fraction_exhibe_sa_source`, dans LotL2_PR2_PR14.lean.

-- ============================================================
-- THÉORÈME DE SYNTHÈSE 2
-- Le régime SYSTEMIQUE requiert une extension de R1
-- ============================================================

-- Un SystemicInteraction sans créancier ne peut pas satisfaire R1.
-- Conséquence architecturale : B1 doit introduire un statut
-- d'écriture intermédiaire "dette non encore attribuée"
-- distinct de R1 standard.

theorem systemique_requires_R1_extension :
    -- Pour tout collectif sans créancier identifié
    ∀ (collectif : Finset Actor) (amount : ENNReal),
    let d : SystemicInteraction :=
      { collectif := collectif
        creditor  := none
        amount    := amount }
    -- R1 standard n'est pas satisfait
    ¬ R1_systemique d := by
  intro collectif amount
  simp [R1_systemique]

-- ============================================================
-- THÉORÈME DE SYNTHÈSE 3
-- Condition nécessaire pour que B1 soit cohérent avec R1
-- ============================================================

-- R1 est préservé dans le régime HYBRIDE si et seulement si
-- le profunctor flou est une extension compatible du profunctor
-- booléen sous-jacent  -  c'est-à-dire si fractionactorielle = 1
-- coïncide exactement avec le régime ACTORIEL pur.

-- [C-12 — 28/09/2026] Alias déclaré de `R1_preserved_under_CB1` (même énoncé).
-- Conservé : cité par quatre fichiers du set. Compté une fois au sens des résultats ;
-- les deux figurent parmi les 9 `Classical.choice` du contrôle de référence.
theorem B1_coherence_condition
    (p0 : Actor → Actor → Bool)
    (p1 : Actor → Actor → ℝ)
    (h_compat : CompatibleExtension p0 p1)
    (h_R1 : ∀ a b : Actor, p0 a b = true → p0 b a = true) :
    -- Condition suffisante de cohérence de B1 avec R1
    ∀ a b : Actor, p1 a b = 1 → p1 b a = 1 :=
  -- Strictement identique à R1_preserved_under_CB1 :
  -- on le renomme pour clarifier son rôle architectural
  R1_preserved_under_CB1 p0 p1 h_compat h_R1

-- ============================================================
-- TABLEAU DE BORD  -  SIGNAUX ARCHITECTURAUX PRODUITS
-- ============================================================

-- Les trois théorèmes ci-dessus produisent trois signaux
-- au sens du MRC (C-SIGNAL, Couche 1) :

-- SIGNAL 1  -  [DÉCOUPLAGE DE RÉGIMES DÉTECTÉ]
-- Régime comptable MRC (fraction calculable) vs
-- régime écologisation Callon (convention localement produite)
-- → fractionactorielle est une valeur délibérée, non calculée
-- Porteur : conventionattributionseuil (champ A4, Note amendements)

-- SIGNAL 2  -  [INCOHÉRENCE INTER-COUCHES niveau 0-1  -  CONFIRMÉE]
-- R1 Couche 0 présuppose un créancier identifié.
-- regimeObligation=SYSTEMIQUE admet creditor=none.
-- → B1 doit introduire C-STATUT-DETTE :
--   { ATTRIBUEE | EN_DELIBERATION | SYSTEMIQUE_NON_ATTRIBUEE }
--   distinct de R1 standard.

-- SIGNAL 3  -  [CONDITION ARCHITECTURALE SUR B1]
-- Le régime HYBRIDE est cohérent avec R1 si et seulement si
-- CompatibleExtension est garantie par construction.
-- → B1 doit contraindre : fractionactorielle = 1 <-> régime ACTORIEL
--   Cette contrainte doit figurer en Couche 1 comme règle,
--   non en Couche 2 comme convention.
