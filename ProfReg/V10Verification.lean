-- V10Verification.lean
import ProfReg.Primitives
import ProfReg.V3Verification
import ProfReg.V4Verification

-- Ouvrir le namespace ProfReg pour accéder à tous les types et théorèmes V3/V4
open ProfReg

namespace V10

-- ─────────────────────────────────────────────────────────────────────────────
-- STRUCTURES
-- ─────────────────────────────────────────────────────────────────────────────

-- ─────────────────────────────────────────────────────────────
-- Types déplacés dans `ProfReg/Primitives.lean` le 7 septembre 2026
-- (tâche 3quinquies). Ils n'ont jamais eu besoin de Mathlib ; seules
-- les preuves de ce fichier en ont besoin. Les séparer supprime la
-- cause des dérives de copies constatées ce jour.
-- ─────────────────────────────────────────────────────────────

-- `PorteeAsymetrie`, `PorteurDID`, `ContextePlanetaire`,
-- `estPlanetaireSansPorteur`, `ReglePlanetaire` : voir Primitives.lean

-- ─────────────────────────────────────────────────────────────────────────────
-- V10a — force deliberation
-- ─────────────────────────────────────────────────────────────────────────────

-- CORRIGÉ le 7 septembre 2026 : `h_statut` n'est plus une hypothèse,
-- il est DÉDUIT de l'hypothèse planétaire via ReglePlanetaire.
theorem V10a_planetaire_force_deliberation
    (c : ContextePlanetaire)
    (h_regle : ReglePlanetaire c)
    (h : estPlanetaireSansPorteur c)
    (n : NiveauRIA)
    (h_valide : transition_valide c.statutDette n) :
    n = NiveauRIA.deliberation :=
  nonattribuee_force_deliberation c.statutDette n (h_regle h) h_valide

-- ─────────────────────────────────────────────────────────────────────────────
-- V10a_neg — critique interdit
-- ─────────────────────────────────────────────────────────────────────────────

theorem V10a_planetaire_critique_interdit
    (c : ContextePlanetaire)
    (h_statut : c.statutDette = StatutDette.nonAttribuee)
    (h_valide : transition_valide c.statutDette NiveauRIA.critique) :
    False := by
  exact cascade_deliberation_before_critique
          c.statutDette NiveauRIA.critique h_statut h_valide rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- V10a_synthese
-- ─────────────────────────────────────────────────────────────────────────────

-- CORRIGÉ le 7 septembre 2026 : même correction que V10a ci-dessus.
theorem V10a_synthese
    (c : ContextePlanetaire)
    (h_regle : ReglePlanetaire c)
    (h : estPlanetaireSansPorteur c) :
    (∀ n, transition_valide c.statutDette n → n = NiveauRIA.deliberation) ∧
    ¬ transition_valide c.statutDette NiveauRIA.critique := by
  have h_statut : c.statutDette = StatutDette.nonAttribuee := h_regle h
  constructor
  · intro n h_valide
    exact nonattribuee_force_deliberation c.statutDette n h_statut h_valide
  · intro h_valide
    exact cascade_deliberation_before_critique
            c.statutDette NiveauRIA.critique h_statut h_valide rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- NOUVEAUX TYPES POUR V10c
-- ─────────────────────────────────────────────────────────────────────────────

-- `HorizonTemporel`, `LegitimiteRepresentant`, `ContexteProspectif`,
-- `exigeRepresentationProspective`, `condRefutationRenseignee` :
-- voir ProfReg/Primitives.lean

-- ─────────────────────────────────────────────────────────────────────────────
-- V10c — REPRESENTATION-PROSPECTIVE comme contrainte de Couche 1
--
-- Énoncé : si horizon = PLANETAIRE et porteur absent,
-- alors legitimite = planetaireNonDesignee ET condRefutation est obligatoire.
--
-- Dépendances : nonattribuee_force_deliberation (V4),
--               structures V10a (PorteurDID, StatutDette)
-- Encodabilité : MOYENNE/HAUTE — nouveau type HorizonTemporel,
--                logique par cas sur LegitimiteRepresentant
-- ─────────────────────────────────────────────────────────────────────────────

-- ┌───────────────────────────────────────────────────────────────────┐
-- │ CONV-6 — la REPRESENTATION-PROSPECTIVE est EXIGÉE, non déduite     │
-- └───────────────────────────────────────────────────────────────────┘
--
-- [THÉORÈME CIRCULAIRE SUPPRIMÉ — 7 septembre 2026, décision du porteur]
-- Le théorème `V10c_representation_prospective_obligatoire` occupait
-- cette place. Il prenait `h_cond : condRefutationRenseignee c` EN
-- HYPOTHÈSE et la restituait dans sa conclusion : il démontrait donc
-- « si la condition de réfutation est renseignée, alors elle est
-- renseignée ». L'obligation -- qu'elle DOIVE l'être -- n'y était
-- jamais établie.  [RAISONNEMENT AUTOREFERENTIEL]
--
-- CONVENTION retenue à sa place :
--   Lorsque HorizonTemporel = PLANETAIRE et que le porteur est
--   structurellement absent, la phase REPRESENTATION-PROSPECTIVE est
--   EXIGÉE et legitimiterepresentant prend la valeur
--   planetaireNonDesignee. C'est une décision de gouvernance
--   (NT-ARCH §5.2, AM-ARCH-01, invariant de Couche 1) : elle se
--   DÉCLARE, elle ne se démontre pas.
--
-- Statut : convention de déclaration, non théorème.
-- Contrepartie formelle : l'obligation qui en découle est démontrée
--   en `ProfReg/PR8_RefutationPratique.lean` --
--   `planetaire_sans_porteur_exige_refutation`, qui prend la présente
--   convention en hypothèse (`RegleAM_ARCH_01`) et CONCLUT la
--   condition de réfutation au lieu de la supposer.

-- ┌───────────────────────────────────────────────────────────────────┐
-- │ CONV-7 — le blocage sans condition de réfutation                   │
-- └───────────────────────────────────────────────────────────────────┘
--
-- [THÉORÈME DÉFECTUEUX SUPPRIMÉ — 7 septembre 2026, décision du porteur]
-- Le théorème `V10c_sans_refutation_bloque` occupait cette place.
-- Son hypothèse `h_no_cond : ¬ condRefutationRenseignee c` n'était PAS
-- UTILISÉE dans sa preuve (`intro h_neg; exact h_neg ⟨h_horizon,
-- h_absent⟩`). Son énoncé se réduisait à `exigeRepresentationProspective
-- c`, déjà donné par les deux autres hypothèses. Rien n'y était
-- « bloqué » : le nom sur-revendiquait.  [ENGAGEMENT SANS SYMETRIE]
--
-- CONVENTION retenue à sa place :
--   Une inscription dont la condition de réfutation n'est pas
--   renseignée est REFUSÉE lorsque la légitimité du représentant est
--   PRATIQUE ou planetaireNonDesignee. Le refus est une règle de
--   gouvernance du registre ; il se déclare.
--
-- Statut : convention de déclaration, non théorème.
-- Contrepartie formelle : `PR8_sans_refutation_bloque`
--   (`ProfReg/PR8_RefutationPratique.lean`) démontre la contraposée --
--   sans condition de réfutation, ni PRATIQUE ni planetaireNonDesignee
--   ne sont inscriptibles. C'est l'énoncé que ce nom promettait.
-- Interdit : citer V10c comme établissant le blocage
--   -> [DECOUPLAGE DE REGIMES DETECTE]

  -- ─────────────────────────────────────────────────────────────────────────────
-- V10b — Commutativité complète NT-G7 ↔ NT-G2 ↔ NT-ARCH
-- STATUT : sorry documenté — hors portée immédiate
--
-- Nécessite : type produit ActeurG7G2 croisant NT-G7 et NT-G2
-- Analogue à : ACT-G2-010 (2-cellule Annexe G, préservation ACTORIEL)
-- Horizon : Vague C.1 du programme MRC v5.5
-- ─────────────────────────────────────────────────────────────────────────────

-- ┌───────────────────────────────────────────────────────────────────┐
-- │ CONV-2 — la commutativité du carré triangulaire est PROCÉDURALE    │
-- └───────────────────────────────────────────────────────────────────┘
--
-- [THÉORÈME CREUX SUPPRIMÉ — 7 septembre 2026, décision du porteur]
-- Le théorème `V10b_commutatif_G7_G2_planetaire : True := by trivial`
-- occupait cette place. Il énonçait `True` : un placeholder assumé, mais
-- qui comptait dans le décompte des théorèmes.
--
-- CONVENTION retenue à sa place :
--   La commutativité du carré NT-G7 <-> NT-G2 <-> NT-ARCH est établie
--   PROCÉDURALEMENT — par V10a et V10c ici, puis par les invariants
--   d'états de V10bVerification.lean. La 2-cellule complète (G.9.3,
--   framed bicategories) reste hors Mathlib, horizon v6.x.
--
-- Statut : convention de déclaration, non théorème.
-- Interdit : écrire « la commutativité de base est prouvée »
--   -> [DÉCOUPLAGE DE RÉGIMES DÉTECTÉ]

end V10
