import ProfReg.V1Verification
import ProfReg.Primitives

namespace ProfReg



inductive PhaseEnquete where
  | inscription           : PhaseEnquete
  | obligationSansPorteur : PhaseEnquete
  | inventaireAssetsActifs: PhaseEnquete
  | deliberation          : PhaseEnquete
  deriving DecidableEq, Repr

-- ─────────────────────────────────────────────────────────────
-- Types déplacés dans `ProfReg/Primitives.lean` le 7 septembre 2026
-- (tâche 3quinquies). Ils n'ont jamais eu besoin de Mathlib ; seules
-- les preuves de ce fichier en ont besoin. Les séparer supprime la
-- cause des dérives de copies constatées ce jour.
-- ─────────────────────────────────────────────────────────────

-- `RegimeObligation` : voir ProfReg/Primitives.lean

structure Interaction where
  regime          : RegimeObligation
  porteurDeclare  : Option String    -- DID porteur, peut être absent
  phase           : PhaseEnquete


def chemin_direct (i : Interaction) : PhaseEnquete :=
  match i.regime, i.porteurDeclare with
  | RegimeObligation.systemique, none =>
      PhaseEnquete.deliberation
  | RegimeObligation.systemique, some _ =>
      PhaseEnquete.deliberation
  | _, _ =>
      i.phase

def chemin_via_inventaire (i : Interaction) : PhaseEnquete :=
  match i.regime with
  | RegimeObligation.systemique =>
      PhaseEnquete.deliberation
  | _ =>
      i.phase

/- [C-1 — 28/09/2026, décision du porteur] `V3_commutatif` est vrai par
   construction : les deux branches systémiques de `chemin_direct` rendent
   `deliberation`, comme `chemin_via_inventaire` (forme 1, patron V10b / B-5).
   Il est conservé comme **lecture des deux définitions** ; il ne prouve pas
   la commutativité du carré B1↔B2 du MRC, qui est **procédurale** et déclarée
   comme telle (NT-ARCH l.667, NT-G2). Le contenu réel est porté par
   `V3_aboutit_deliberation` et `V3_actoriel_inchange`. -/
theorem V3_commutatif (i : Interaction)
    (h : i.regime = RegimeObligation.systemique) :
    chemin_direct i = chemin_via_inventaire i := by
  simp [chemin_direct, chemin_via_inventaire, h]
  cases i.porteurDeclare <;> simp


theorem V3_aboutit_deliberation (i : Interaction)
    (h : i.regime = RegimeObligation.systemique) :
    chemin_direct i = PhaseEnquete.deliberation := by
  simp [chemin_direct, h]
  cases i.porteurDeclare <;> simp


theorem V3_actoriel_inchange (i : Interaction)
    (h : i.regime = RegimeObligation.actoriel) :
    chemin_direct i = i.phase ∧
    chemin_via_inventaire i = i.phase := by
  simp [chemin_direct, chemin_via_inventaire, h]

end ProfReg
