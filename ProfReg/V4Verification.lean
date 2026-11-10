import ProfReg.V3Verification
import ProfReg.Primitives

namespace ProfReg

-- ============================================================
-- V4  -  Cascade R-INTERDIT-ABSOLU en régime SYSTEMIQUE
-- Source : Note amendements v5.4, §III.2 (Tension T3)
-- ============================================================

-- ============================================================
-- TYPES DE BASE  -  nouveaux pour V4
-- ============================================================

-- ─────────────────────────────────────────────────────────────
-- Types déplacés dans `ProfReg/Primitives.lean` le 7 septembre 2026
-- (tâche 3quinquies). Ils n'ont jamais eu besoin de Mathlib ; seules
-- les preuves de ce fichier en ont besoin. Les séparer supprime la
-- cause des dérives de copies constatées ce jour.
-- ─────────────────────────────────────────────────────────────

-- `StatutDette`, `NiveauRIA`, `InventaireNonVide` et la machine
-- d'états `transition_valide` : voir ProfReg/Primitives.lean

-- ============================================================
-- THÉORÈME V4a
-- Inventaire non vide requis avant tout déclenchement
-- ============================================================

-- Définir l'inventaire comme sous-type garantit V4a par construction :
-- il est impossible de construire un InventaireNonVide vide

-- [C-2 — 28/09/2026] `inventaire_nonempty_required` est une **lecture du
-- type** (projection du sous-type, forme 3 logée dans le type, patron B-6).
-- Sa portée est témoignée, sur le modèle de V1, par
-- `inventaire_nonempty_discrimine` : le type est habité, et la contrainte
-- n'est pas vide de contenu (la liste vide est exclue).
theorem inventaire_nonempty_required (inv : InventaireNonVide) :
    inv.val ≠ [] :=
  inv.property

/-- Témoins de `inventaire_nonempty_required` (C-2, 28/09/2026) :
    (1) un inventaire non vide existe — témoin bien formé ;
    (2) une liste du type sous-jacent échoue le prédicat — témoin
        discriminant : la liste vide n'est pas un `InventaireNonVide`. -/
theorem inventaire_nonempty_discrimine :
    Nonempty InventaireNonVide ∧ ∃ l : List String, ¬ (l ≠ []) :=
  ⟨⟨⟨["did:mrc:usine-A"], List.cons_ne_nil _ _⟩⟩, ⟨[], fun h => h rfl⟩⟩

-- Exemple : construire un inventaire valide
def exemple_inventaire : InventaireNonVide :=
  ⟨["did:mrc:usine-A", "did:mrc:usine-B"], by simp⟩

-- Vérifier qu'un inventaire vide est non constructible
-- (la contrainte est dans le type lui-même)
example : exemple_inventaire.val ≠ [] := by
  simp [exemple_inventaire]

-- ============================================================
-- THÉORÈME V4b
-- NONATTRIBUEE → niveau CRITIQUE est formellement inaccessible
-- ============================================================

theorem cascade_deliberation_before_critique
    (statut : StatutDette)
    (niveau : NiveauRIA)
    (h_nonatt : statut = StatutDette.nonAttribuee)
    (h_valide : transition_valide statut niveau) :
    niveau ≠ NiveauRIA.critique := by
  intro h_critique
  rw [h_nonatt, h_critique] at h_valide
  exact h_valide    -- transition_valide nonAttribuee critique = False

-- Corollaire : NONATTRIBUEE force DELIBERATION
theorem nonattribuee_force_deliberation
    (statut : StatutDette)
    (niveau : NiveauRIA)
    (h_nonatt : statut = StatutDette.nonAttribuee)
    (h_valide : transition_valide statut niveau) :
    niveau = NiveauRIA.deliberation := by
  cases niveau with
  | deliberation => rfl
  | critique =>
      exfalso
      exact cascade_deliberation_before_critique
              statut NiveauRIA.critique h_nonatt h_valide rfl

-- ============================================================
-- THÉORÈME V4c
-- Désignation d'un porteur libère le niveau CRITIQUE
-- ============================================================

/-- **CORRIGÉ le 7 septembre 2026 — décision du porteur.**

    La version antérieure concluait `∃ n, n = critique ∧ transition_valide
    statut_apres n` et n'utilisait QUE `h_transition` : `inv` et `h_delib`
    étaient inertes (signalées par le linter `unusedVariables`). Elle
    n'établissait donc pas ce que son titre annonce — ni l'inventaire non
    vide, ni le passage préalable par la délibération n'y jouaient de rôle.
    [ENGAGEMENT SANS SYMÉTRIE]

    La version ci-dessous emploie les trois hypothèses et dit ce que
    « libérer » veut dire : **avant la désignation, CRITIQUE est fermé ;
    après, il est ouvert ; et l'inventaire est renseigné.** C'est un
    passage de fermé à ouvert, non une simple accessibilité. -/
theorem critique_released_by_porteur
    (statut_avant : StatutDette)
    (statut_apres : StatutDette)
    (inv          : InventaireNonVide)
    (h_delib      : statut_avant = StatutDette.enDeliberation)
    (h_transition : statut_apres = StatutDette.attribuee) :
    ¬ transition_valide statut_avant NiveauRIA.critique
    ∧ transition_valide statut_apres NiveauRIA.critique
    ∧ inv.val ≠ [] := by
  refine ⟨?_, ?_, inv.property⟩
  · rw [h_delib]; simp [transition_valide]
  · rw [h_transition]; simp [transition_valide]

-- ============================================================
-- THÉORÈME DE SYNTHÈSE V4
-- La cascade complète est cohérente
-- ============================================================

-- Toute interaction systémique sans porteur passe par DELIBERATION
-- avant d'atteindre CRITIQUE  -  jamais directement
theorem V4_cascade_coherente
    (statut_initial : StatutDette)
    (h_init : statut_initial = StatutDette.nonAttribuee) :
    -- CRITIQUE est inaccessible depuis NONATTRIBUEE
    ¬ transition_valide statut_initial NiveauRIA.critique ∧
    -- DELIBERATION est l'unique transition autorisée
    transition_valide statut_initial NiveauRIA.deliberation := by
  constructor
  · rw [h_init]
    simp [transition_valide]
  · rw [h_init]
    simp [transition_valide]
