-- V4cVerification.lean
-- Préservation du régime ACTORIEL par la transition V4c (ENDELIBERATION → ATTRIBUEE)
-- ACT-G2-010 — résolution partielle procédurale
-- Régime vérifiabilité-cohérence : preuve structurelle, non 2-cellule ProfReg complète

-- [D-14, 27/09/2026] `import Mathlib.Tactic` retiré : superflu — le fichier compile
-- et s'audite à l'identique sans lui (vérifié les 26 et 27/09).
import ProfReg.V3Verification  -- RegimeObligation, PhaseEnquete
import ProfReg.V4Verification  -- StatutDette, NiveauRIA, transition_valide

open ProfReg

namespace V4c

/-- Un état couplé associe un régime d'obligation à un statut de dette.
    Modélise le couple (regimeObligation, statutDette) d'un acteur inscrit. -/
structure EtatCouple where
  regime  : RegimeObligation
  statut  : StatutDette

/-- La transition V4c : ENDELIBERATION → ATTRIBUEE (seule transition autorisée
    depuis enDeliberation vers attribuee, cf. critiqueReleasedByPorteur). -/
def transitionV4c (e : EtatCouple) : EtatCouple :=
  match e.statut with
  | StatutDette.enDeliberation => { e with statut := StatutDette.attribuee }
  | _                          => e   -- identité sur tout autre statut

/-- THÉORÈME PRINCIPAL — ACT-G2-010 résolution procédurale
    La transition V4c préserve le régime ACTORIEL :
    si l'état d'entrée a regimeObligation = actoriel,
    l'état de sortie a regimeObligation = actoriel. -/
-- [R-7 (iii) — 28/09/2026] Forme 1 déclarée, par cohérence avec C-10 (son alias
-- `V4c_actoriel_preserved_alias` et `V4c_regime_unchanged` le sont déjà) :
-- `transitionV4c` ne met à jour que `statut` ; l'invariance du régime est une
-- lecture de la définition, sans témoin que la transition modifie autre chose.
-- ACT-G2-010 reste une résolution **procédurale** (NT-G2).
theorem V4c_actoriel_preserved (e : EtatCouple)
    (h : e.regime = RegimeObligation.actoriel) :
    (transitionV4c e).regime = RegimeObligation.actoriel := by
  unfold transitionV4c
  split
  · -- cas enDeliberation : le champ `regime` est préservé par la mise à jour de `statut`
    simp [h]
  · -- cas identité : l'état est inchangé
    exact h

/-- Corollaire : V4c n'introduit aucun effet de bord sur le régime
    (généralisation à tout régime, pas seulement ACTORIEL). -/
-- [C-10 — 28/09/2026] Forme 1 déclarée : `transitionV4c` ne met à jour que
-- `statut` ; l'invariance du régime est une lecture de la définition. V4c est
-- déjà une résolution **procédurale** (ACT-G2-010).
theorem V4c_regime_unchanged (e : EtatCouple) :
    (transitionV4c e).regime = e.regime := by
  unfold transitionV4c
  split <;> simp

/-- Connexion avec V3_actoriel_inchange :
    V4c satisfait la même garantie de non-modification du régime
    que celle prouvée pour B1+B2 dans V3Verification.

    [C-10 — 28/09/2026] Renommé (ex-`V4c_coherent_avec_V3`) : l'énoncé est un
    **alias** de `V4c_actoriel_preserved` (même énoncé, preuve par renvoi). Le nom
    ancien se réclamait d'une cohérence avec V3, dont la commutativité est
    procédurale depuis C-1 ; le parallèle avec `V3_actoriel_inchange` n'est que
    de forme (V3 porte sur la phase, V4c sur le régime). -/
theorem V4c_actoriel_preserved_alias
    (e : EtatCouple)
    (h : e.regime = RegimeObligation.actoriel) :
    (transitionV4c e).regime = RegimeObligation.actoriel := by
  exact V4c_actoriel_preserved e h

end V4c
