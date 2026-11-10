/-
  PR-41 · L'arbitrage de l'écart par un tiers (ISA 505)
  =====================================================

  Porteur : Pierre Musseau. Écrit le 30 septembre 2026, sur décision D-ED-12.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR40_StatutDeLEcart`.

  LE PROBLÈME
  -----------
  PR-40 qualifie l'écart (constaté, non vérifiable, refusé, contesté) sans le
  trancher. L'objection ouverte de la fiche AX-15 demeurait : dans le
  rapprochement bancaire, « le relevé de la banque fait foi contre
  l'entreprise » ; transposé, le registre du plus fort ferait foi contre
  celui du plus faible.

  L'ANCRAGE (fiche AX-16 — versée le 30/09, D-ED-19)
  -------------------------------------------------
  ISA 505, *External Confirmations* (texte publié par l'IRE) :
    §2  « Audit evidence is more reliable when it is obtained from
         independent sources outside the entity » ;
    §6  « Exception: A response that indicates a difference between
         information requested to be confirmed, or contained in the entity's
         records, and information provided by the confirming party » ;
    §7  « the auditor shall maintain control over external confirmation
         requests » ;
    §8  refus de la direction : « Inquire as to management's reasons for the
         refusal, and seek audit evidence as to their validity and
         reasonableness » ; §9 : à défaut, « communicate with those charged
         with governance » ;
    §10 doute sur la fiabilité : « obtain further audit evidence » ;
    §12 non-réponse : « perform alternative audit procedures » ;
    §14 « The auditor shall investigate exceptions ».
  Et le CR 2026-S09 du porteur : « faire auditer par la communauté de
  contrôle les enregistrements avancés — si possible vérifier que les
  enregistrements duaux ont bien été effectués avec les autres entités ».

  LA RÈGLE FORMALISÉE
  -------------------
  1. AUCUN TENEUR NE TRANCHE : une investigation conduite par A ou par B
     laisse le statut inchangé.
  2. Le tiers doit être NON LIÉ aux deux teneurs (au sens d'ISA 550 §10(b) :
     notamment une entité « under common control ») ; le lien est une donnée
     DÉCLARÉE de l'investigation.
  3. Le tiers CONFIRME la ligne de A, l'INFIRME, ou NE CONCLUT PAS.
  4. L'INFIRMATION N'EFFACE PAS : la ligne reste inscrite, avec son statut
     arbitré. Le registre garde la trace (D-ED-3, écart inscrit, jamais
     effacé).

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne dit pas QUI est le tiers dans un registre de communalité — la
    « communauté de contrôle » du CR S09 est un candidat ; elle n'est pas
    instituée ici. [D-ED-37 — 30/09/2026] Instituée par CONV-16 / PR-43 (D-ED-20).
  · Il ne vérifie pas la non-liaison : c'est une déclaration de
    l'investigation, que le modèle suppose sincère.
  · Il ne transpose pas ISA 505 hors de l'audit des états financiers : la
    transposition est déclarée dans la fiche AX-16.
-/

import ProfReg.PR40_StatutDeLEcart

namespace ProfRegPR41

open ProfRegPR35 (Entite Registre Ligne)
open ProfRegPR40 (StatutEcart Communication ecartQualifie)

/-! ## 1. L'investigation -/

inductive Issue where
  | confirme    -- le tiers confirme la ligne de A : B devait inscrire le miroir
  | infirme     -- le tiers infirme la ligne de A
  | nonConclu   -- éléments insuffisants (ISA 505 §10, §12)
  deriving DecidableEq, Repr

structure Investigation where
  tiers : Entite
  /-- Le tiers est-il lié à l'un des teneurs (ISA 550 §10(b)) ? Déclaré. -/
  lie   : Bool
  issue : Issue
  deriving DecidableEq, Repr

/-- Le tiers est recevable : ni A, ni B, et non lié. -/
def tiersRecevable (inv : Investigation) (a b : Entite) : Bool :=
  !(inv.tiers == a) && !(inv.tiers == b) && !inv.lie

inductive StatutArbitre where
  | nonArbitre (s : StatutEcart)        -- aucune investigation recevable
  | confirmeParTiers
  | infirmeParTiers
  | investigueNonConclu (s : StatutEcart)
  deriving DecidableEq, Repr

/-- **Le statut après investigation.** Une investigation irrecevable (par un
    teneur, ou par un tiers lié) est sans effet. -/
def arbitrer (s : StatutEcart) (inv : Option Investigation) (a b : Entite) : StatutArbitre :=
  match inv with
  | none => .nonArbitre s
  | some i =>
    if tiersRecevable i a b then
      match i.issue with
      | .confirme  => .confirmeParTiers
      | .infirme   => .infirmeParTiers
      | .nonConclu => .investigueNonConclu s
    else .nonArbitre s

/-- L'écart arbitré : chaque ligne de l'écart qualifié (PR-40), avec son
    statut arbitré. Une investigation au plus par ligne, donnée par `inv`. -/
def ecartArbitre {V : Type} (com : Communication) (RA RB : Registre V)
    (inv : Ligne V → Option Investigation) : List (Ligne V × StatutArbitre) :=
  (ecartQualifie com RA RB).map
    (fun p => (p.1, arbitrer p.2 (inv p.1) RA.teneur RB.teneur))

/-! ## 2. Ce qui se démontre -/

/-- **Aucun teneur ne tranche.** Une investigation conduite par A ou par B
    laisse l'écart non arbitré. -/
theorem aucun_teneur_ne_tranche (s : StatutEcart) (a b : Entite) (l : Bool) (iss : Issue) :
    arbitrer s (some ⟨a, l, iss⟩) a b = .nonArbitre s
    ∧ arbitrer s (some ⟨b, l, iss⟩) a b = .nonArbitre s := by
  -- `decide_eq_true rfl` plutôt que `beq_self_eq_true` : l'instance
  -- `LawfulBEq Nat` de la bibliothèque tire `Classical.choice`.
  have ha : (a == a) = true := decide_eq_true rfl
  have hb : (b == b) = true := decide_eq_true rfl
  constructor
  · show (if (!(a == a) && !(a == b) && !l) = true then _ else _) = _
    rw [ha]; rfl
  · show (if (!(b == a) && !(b == b) && !l) = true then _ else _) = _
    rw [hb, Bool.not_true, Bool.and_false, Bool.false_and]; rfl

/-- **Un tiers lié ne tranche pas** (ISA 550 §10(b)). -/
theorem un_tiers_lie_ne_tranche_pas (s : StatutEcart) (a b t : Entite) (iss : Issue) :
    arbitrer s (some ⟨t, true, iss⟩) a b = .nonArbitre s := by
  simp [arbitrer, tiersRecevable]

/-- **L'arbitrage ne change pas l'écart** : les lignes arbitrées sont
    exactement celles de l'écart de PR-35. L'infirmation n'efface rien. -/
theorem l_arbitrage_n_efface_rien {V : Type} (com : Communication) (RA RB : Registre V)
    (inv : Ligne V → Option Investigation) :
    (ecartArbitre com RA RB inv).map Prod.fst = ProfRegPR35.ecart RA RB := by
  unfold ecartArbitre
  rw [List.map_map]
  have := ProfRegPR40.la_communication_ne_change_pas_l_ecart com RA RB
  rw [← this]
  rfl

/-! ## 3. Instance : l'entreprise, le fournisseur qui nie, un tiers -/

def entreprise : Entite := 2
def fournisseur : Entite := 40
def communauteDeControle : Entite := 50

open ProfRegPR40 (regA regBNie)

/-- **PR-41 — le tiers tranche la contestation.** Le fournisseur nie
    (statut `conteste`, PR-40) ; la communauté de contrôle, non liée,
    confirme la ligne de l'entreprise. -/
theorem le_tiers_tranche_la_contestation :
    ecartArbitre .extraitCommunique regA regBNie
        (fun _ => some ⟨communauteDeControle, false, .confirme⟩)
      = [(⟨fournisseur, .Dplus, 10⟩, .confirmeParTiers)] := by
  decide

/-- **Et l'infirmation laisse la ligne inscrite**, avec son statut. -/
theorem l_infirmation_laisse_la_ligne_inscrite :
    ecartArbitre .extraitCommunique regA regBNie
        (fun _ => some ⟨communauteDeControle, false, .infirme⟩)
      = [(⟨fournisseur, .Dplus, 10⟩, .infirmeParTiers)] := by
  decide

/-- **Témoin discriminant** (R-7) de `arbitrer` : sur le même écart
    contesté, le teneur ne tranche pas, le tiers lié non plus, le tiers
    recevable confirme, infirme, ou ne conclut pas. -/
theorem arbitrer_temoin_discriminant :
    arbitrer .conteste (some ⟨entreprise, false, .confirme⟩) entreprise fournisseur
      = .nonArbitre .conteste
    ∧ arbitrer .conteste (some ⟨communauteDeControle, true, .confirme⟩) entreprise fournisseur
      = .nonArbitre .conteste
    ∧ arbitrer .conteste (some ⟨communauteDeControle, false, .confirme⟩) entreprise fournisseur
      = .confirmeParTiers
    ∧ arbitrer .conteste (some ⟨communauteDeControle, false, .infirme⟩) entreprise fournisseur
      = .infirmeParTiers
    ∧ arbitrer .conteste (some ⟨communauteDeControle, false, .nonConclu⟩) entreprise fournisseur
      = .investigueNonConclu .conteste := by
  decide

end ProfRegPR41
