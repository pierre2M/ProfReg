-- V10bVerification.lean
-- Carré triangulaire NT-G7 ↔ NT-G2 ↔ NT-ARCH (V10b) — PROCÉDURAL (CONV-2)
-- Vague C.1 — construction ex novo du type produit ActeurG7G2
-- [B-5 — 28/09/2026, décision du porteur] Ce fichier ne contient plus aucun
-- théorème : les deux énoncés de commutation sont retirés (voir plus bas) et
-- rattachés à CONV-2. Le type produit et ses projections sont conservés.

-- [D-14, 27/09/2026] `import Mathlib.Tactic` retiré : superflu — le fichier compile
-- et s'audite à l'identique sans lui (vérifié les 26 et 27/09).
import ProfReg.V1Verification   -- ActeurF4Coherent, AppelImmanent, PuissanceAffirmative
import ProfReg.V3Verification   -- RegimeObligation, PhaseEnquete
import ProfReg.V4Verification   -- StatutDette, NiveauRIA, transition_valide
import ProfReg.V10Verification  -- ContextePlanetaire, HorizonTemporel, LegitimiteRepresentant

open ProfReg

namespace V10b

/-- Type produit couplant NT-G7 (capabilités) et NT-G2 (responsabilité).
    Représente un acteur inscrit simultanément dans G-JUSTICE et G-RESPONSABILITE.
    Source : R-HABITABILITE-CAPABILITE (NT-G2 §3.2) + C-CAPABILITES (NT-G7 §3.1) -/
structure ActeurG7G2 where
  -- Composante NT-G2 : régime d'obligation et statut de dette
  regimeObl    : RegimeObligation
  statutDette  : StatutDette
  -- Composante NT-G7 : capabilité plancher menacée (booléen simplifié)
  capabiliteMenacee : Bool
  -- Seuil d'entrée communauté morale (couche 0, NT-ARCH §6.1)
  -- SENTIENCE | FINALITEIMMANENTE | NONDECLARE
  seuilEntre   : Fin 3  -- 0 = SENTIENCE, 1 = FINALITEIMMANENTE, 2 = NONDECLARE

/-- Projection vers NT-G2 : extrait le sous-état responsabilité -/
def projG2 (a : ActeurG7G2) : RegimeObligation × StatutDette :=
  (a.regimeObl, a.statutDette)

/-- Projection vers NT-ARCH : extrait le régime d'obligation seul
    (invariant B1 : fraction = 1 ↔ ACTORIEL) -/
def projARCH (a : ActeurG7G2) : RegimeObligation :=
  a.regimeObl

/-- Projection vers NT-G7 : extrait l'état capabilité + seuil
    (R-HABITABILITE-CAPABILITE conditionne seuilEntre ≠ NONDECLARE) -/
def projG7 (a : ActeurG7G2) : Bool × Fin 3 :=
  (a.capabiliteMenacee, a.seuilEntre)

-- ┌───────────────────────────────────────────────────────────────────┐
-- │ CONV-2 — commutation du carré triangulaire : procédurale           │
-- └───────────────────────────────────────────────────────────────────┘
--
-- [FORME 1 RETIRÉE — 28 septembre 2026, décision du porteur (audit B-5)]
-- `V10b_triangle_commutatif` et son corollaire `V10b_actoriel_stable`
-- occupaient cette place. Le trajet direct était écrit
--   if a.capabiliteMenacee && a.seuilEntre.val ≠ 2
--   then a.regimeObl else a.regimeObl
-- — DEUX BRANCHES IDENTIQUES. L'égalité avec le trajet via NT-G2
-- (`(projG2 a).1 = a.regimeObl`) était donc vraie par écriture, pour tout
-- acteur : forme 1 (NT-ARCH §8ter). Ce qu'elle devait établir —
-- R-HABITABILITE-CAPABILITE ne modifie pas regimeObligation — était
-- inscrit dans la définition, non démontré.
--
-- CE QUE DIT LA RÈGLE (NT-G2 §3.2, relu le 28/09) : son action porte sur
-- C-CAPABILITES (inscription automatique), déclenche R-CAPABILITES (F6)
-- et alerte F4 ; elle ne touche pas au régime d'obligation. La
-- non-interférence est une propriété d'ARCHITECTURE : elle se déclare.
--
-- CONVENTION : CONV-2 (Annexe méthodologique, table des conventions) —
--   « la commutativité du carré triangulaire NT-G7 ↔ NT-G2 ↔ NT-ARCH est
--     procédurale, non formelle ». Elle couvre désormais aussi ce retrait.
-- Interdit : citer V10b comme commutativité PROUVÉE
--   -> [DECOUPLAGE DE REGIMES DETECTE]

-- ┌───────────────────────────────────────────────────────────────────┐
-- │ CONV-8 — seuil NONDECLARE et signal DELIBERATION                   │
-- └───────────────────────────────────────────────────────────────────┘
--
-- [TAUTOLOGIE SUPPRIMÉE — 7 septembre 2026, décision du porteur]
-- Le théorème `V10b_seuil_nondeclare_force_deliberation` occupait cette
-- place. Ses TROIS hypothèses (`hCap`, `hSeuil`, `hSyst`) étaient
-- inutilisées -- signalées par le linter `unusedVariables` -- et sa
-- conclusion était une disjonction sur les TROIS constructeurs de
-- `StatutDette`, donc vraie de tout. Sa preuve était un `cases` rendant
-- le constructeur courant. Son propre commentaire l'admettait :
--   « Ici on admet pour l'instant que tous les trois états sont
--     possibles ; la preuve se fait par simple analyse de cas ».
-- Le nom annonçait « force_deliberation » : c'est exactement ce qu'il
-- n'établissait pas.
--
-- LE SET LE SAVAIT ET L'AVAIT ÉCRIT. NT-ARCH §8, réserve de portée :
--   « tautologie structurelle (exhaustivité de StatutDette) ; il
--     n'établit pas l'exclusion ATTRIBUEE + seuil NONDECLARE ».
-- C'est la garde qui manquait à V10c, et c'est le précédent qui a permis
-- de repérer les autres.
--
-- CONVENTION retenue à sa place :
--   En régime SYSTEMIQUE, une capabilité menacée avec
--   seuilEntre = NONDECLARE appelle un signal DELIBERATION avant
--   inscription (NT-ARCH §6.1). C'est une règle de gouvernance :
--   elle se déclare, elle ne se démontre pas ici.
--
-- Statut : convention de déclaration, non théorème.
-- Contrepartie formelle existante :
--   · `ProfReg.nonattribuee_force_deliberation` (V4) démontre le
--     forçage vers DELIBERATION à partir du statut nonAttribuee ;
--   · `V10.V10a_planetaire_force_deliberation` le fait dériver d'une
--     règle d'architecture déclarée (`ReglePlanetaire`) plutôt que
--     d'une hypothèse inerte -- c'est le patron à suivre si l'on veut
--     un jour un vrai théorème ici : déclarer la règle
--     « seuilEntre = NONDECLARE et regimeObl = systemique implique
--       statutDette = nonAttribuee », puis conclure par V4.
-- Interdit : citer V10b comme établissant le forçage
--   -> [DECOUPLAGE DE REGIMES DETECTE]

end V10b
