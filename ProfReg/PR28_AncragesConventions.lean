import ProfReg.Primitives
import ProfReg.V4Verification
import ProfReg.PR8_RefutationPratique
import ProfReg.PR27_Candidats_Septembre
/-!
# PR-28 — Ancrages de conventions (CONV-4, CONV-6, CONV-8, CONV-14)

28 septembre 2026. Décision du porteur (suites de l'audit du 26/09, instruction
§2.2) : ancrer les conventions pour lesquelles un théorème de bonne formation
est possible, sur le patron « trou / satisfiabilité / morsure / garde » de PR-23.

**Une convention se déclare ; elle ne se démontre pas.** Ces théorèmes
établissent la **forme** de chaque obligation — qu'elle trie, qu'elle est
satisfiable, ce qu'elle n'exige pas —, jamais qu'elle est juste.
`[RÉSERVE DE MODÈLE]` Les structures ci-dessous sont les miennes ; une autre
transcription des conventions donnerait d'autres théorèmes.
-/

namespace ProfRegPR28

open ProfReg V10

/-! ## 1. CONV-8 — la moitié positive : le non-déclaré appelle la délibération

Patron `V10a_planetaire_force_deliberation` (Annexe §A.15.3) : déclarer la
règle d'architecture, puis conclure par V4. -/

structure SeuilContexte where
  seuil       : SeuilCommunauteMorale
  statutDette : StatutDette

/-- **Règle d'architecture CONV-8, déclarée** (elle ne se démontre pas) : un
    seuil `NONDECLARE` met l'obligation en `nonAttribuee`. -/
def RegleCONV8 (c : SeuilContexte) : Prop :=
  c.seuil = SeuilCommunauteMorale.nonDeclare → c.statutDette = StatutDette.nonAttribuee

/-- **CONV-8 (moitié positive).** Sous la règle déclarée, un seuil `NONDECLARE`
    ne rend accessible que la délibération. -/
theorem nondeclare_force_deliberation (c : SeuilContexte) (h_regle : RegleCONV8 c)
    (h : c.seuil = SeuilCommunauteMorale.nonDeclare) (n : NiveauRIA)
    (h_valide : transition_valide c.statutDette n) : n = NiveauRIA.deliberation :=
  nonattribuee_force_deliberation c.statutDette n (h_regle h) h_valide

/-- **Témoins** (R-2) : la règle n'est pas vide — elle exclut un contexte — et,
    un seuil déclaré, le niveau critique reste accessible. -/
theorem CONV8_temoin_discriminant :
    (¬ RegleCONV8 ⟨SeuilCommunauteMorale.nonDeclare, StatutDette.attribuee⟩)
    ∧ (RegleCONV8 ⟨SeuilCommunauteMorale.sentience, StatutDette.attribuee⟩
       ∧ transition_valide StatutDette.attribuee NiveauRIA.critique) :=
  ⟨(fun h => nomatch (h rfl)),
   (fun h => nomatch h), trivial⟩

/-! ## 2. CONV-6 — la représentation prospective

`[RÉSERVE DE MODÈLE]` « Engager au-delà de l'exercice » est lu comme un horizon
autre qu'`institutionnel`. -/

structure EcritureEngagee where
  ctx                       : ContexteProspectif
  representationProspective : Option String

def EngageAuDelaDeLExercice (e : EcritureEngagee) : Prop :=
  e.ctx.horizon ≠ HorizonTemporel.institutionnel

def SatisfaitCONV6 (e : EcritureEngagee) : Prop :=
  EngageAuDelaDeLExercice e → e.representationProspective ≠ none

/-- **Le trou.** La bonne formation de PR-8 (condition de réfutation) ne porte pas
    CONV-6 : une écriture bien formée au sens de PR-8, engageant au-delà de
    l'exercice, peut n'avoir aucune représentation prospective. -/
theorem BienFormee_ne_borne_pas_la_prospective :
    ∃ e : EcritureEngagee, ProfRegPR8.BienFormee e.ctx ∧ EngageAuDelaDeLExercice e
      ∧ ¬ SatisfaitCONV6 e :=
  ⟨⟨⟨StatutDette.attribuee, HorizonTemporel.intergenerationnel, some "did:x",
     LegitimiteRepresentant.pratique, some "condition"⟩, none⟩,
   (fun _ h => nomatch h),
   (fun h => nomatch h),
   fun h => h (fun h' => nomatch h') rfl⟩

/-- **Satisfiabilité.** La même écriture, avec une représentation prospective. -/
theorem CONV6_est_satisfiable :
    ∃ e : EcritureEngagee, ProfRegPR8.BienFormee e.ctx ∧ EngageAuDelaDeLExercice e
      ∧ SatisfaitCONV6 e :=
  ⟨⟨⟨StatutDette.attribuee, HorizonTemporel.intergenerationnel, some "did:x",
     LegitimiteRepresentant.pratique, some "condition"⟩, some "representation"⟩,
   (fun _ h => nomatch h),
   (fun h => nomatch h),
   (fun _ h => nomatch h)⟩

/-- **Garde de portée.** CONV-6 ne vaut pas dans l'exercice : une écriture à
    horizon institutionnel la satisfait toujours. Lecture de `SatisfaitCONV6` ;
    témoin discriminant : `BienFormee_ne_borne_pas_la_prospective` (R-7). -/
theorem CONV6_ne_vaut_pas_dans_l_exercice (e : EcritureEngagee)
    (h : e.ctx.horizon = HorizonTemporel.institutionnel) : SatisfaitCONV6 e :=
  fun h_au_dela => absurd h h_au_dela

/-! ## 3. CONV-4 bornée — la source déclarée et vérifiable

Les quatre propriétés du bornage du 19/09 : désignation stable, résolution
déclarée, vérification d'intégrité, porteur nommé et réfutable ; le DID est une
forme possible, non la forme obligatoire. -/

inductive FormeDesignation where
  | did | doi | urlArchivee | referenceEditeur | autre
  deriving DecidableEq, Repr

structure SourceDeclaree where
  designation : Option String
  forme       : FormeDesignation
  resolution  : Option String
  integrite   : Option String
  porteur     : Option String

def SatisfaitCONV4 (s : SourceDeclaree) : Prop :=
  s.designation ≠ none ∧ s.resolution ≠ none ∧ s.integrite ≠ none ∧ s.porteur ≠ none

/-- **Satisfiable sans DID** (patron `CONV11_satisfaite_sans_registre_financier`). -/
theorem CONV4_satisfaite_sans_DID :
    ∃ s : SourceDeclaree, SatisfaitCONV4 s ∧ s.forme ≠ FormeDesignation.did :=
  ⟨⟨some "10.3917/xyz", FormeDesignation.doi, some "resolveur", some "empreinte",
    some "porteur"⟩,
   ⟨(fun h => nomatch h), (fun h => nomatch h),
    (fun h => nomatch h), (fun h => nomatch h)⟩,
   (fun h => nomatch h)⟩

/-- **La clause du porteur mord** : trois propriétés sur quatre ne suffisent pas. -/
theorem source_sans_porteur_mal_formee :
    ∃ s : SourceDeclaree, s.designation ≠ none ∧ s.resolution ≠ none
      ∧ s.integrite ≠ none ∧ ¬ SatisfaitCONV4 s :=
  ⟨⟨some "10.3917/xyz", FormeDesignation.doi, some "resolveur", some "empreinte", none⟩,
   (fun h => nomatch h), (fun h => nomatch h),
   (fun h => nomatch h), fun h => h.2.2.2 rfl⟩

/-- **Garde** : CONV-4 ne prescrit aucune forme — chacune est compatible. -/
theorem CONV4_ne_prescrit_aucune_forme (f : FormeDesignation) :
    ∃ s : SourceDeclaree, SatisfaitCONV4 s ∧ s.forme = f :=
  ⟨⟨some "designation", f, some "resolveur", some "empreinte", some "porteur"⟩,
   ⟨(fun h => nomatch h), (fun h => nomatch h),
    (fun h => nomatch h), (fun h => nomatch h)⟩, rfl⟩

/-! ## 4. CONV-14 — la garde de portée

Le premier ancrage existe depuis le 28/09 (D-12) : `le_score_ne_determine_pas_les_axes`
(PR-27). La garde manquait : CONV-14 interdit le score, **non la comparaison sur
un axe**, qui reste possible et sensée (Annexe §A.15.7, *Portée*). -/

open ProfRegPR27 in
/-- **La comparaison sur un axe n'est pas le classement** : un profil peut être
    moindre sur un axe et supérieur au score. La comparaison axe par axe porte une
    information que le score ne donne pas. -/
theorem la_comparaison_sur_un_axe_n_est_pas_le_classement :
    ∃ p q : Profil, p.axe1 < q.axe1 ∧ score q < score p :=
  ⟨⟨0, 5, 5⟩, ⟨1, 0, 0⟩, by decide, by decide⟩

end ProfRegPR28
