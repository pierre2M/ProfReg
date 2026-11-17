/-
  PR-35 · `EcritureDuale` — l'écriture duale ENTRE DEUX TENEURS (N2)
  ===================================================================

  Porteur : Pierre Musseau. Écrit le 29 septembre 2026, sur décisions
  D-ED-1 à D-ED-6 (`MRC/Note_Desambiguisation_Ecriture_Duale_2026-09-29.md`).
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR20_MiroirInterActeurs`
  (pour `TypageIA`, `miroirIA`, `roleDeTypage`).

  L'ÉNONCÉ DU PORTEUR (D-ED-1)
  ----------------------------
  Quand une entité A inscrit dans son registre de communalité une
  responsabilité envers une entité B (débit chez A), B inscrit dans son
  propre registre l'écriture symétrique envers A (crédit chez B), et
  réciproquement. L'écriture duale est un ACCORD ENTRE DEUX TENEURS ; elle
  peut échouer ; son accomplissement est vérifiable par audit.
  — CR 2026-S09 « OKR et comptabilité mésologique », l. 18-30.

  Trois propriétés : (i) deux registres, deux teneurs distincts ;
  (ii) typage opposé ; (iii) symétrie contrôlable, non acquise.

  LECTURE RETENUE (D-ED-3) : RÉCONCILIATION AVEC ÉCART AUDITÉ
  ------------------------------------------------------------
  L'écriture duale n'est PAS une condition de bonne formation d'une
  inscription (cela rendrait impossible l'entité qui refuse, « catégorie C »
  du CR S09). C'est une PROPRIÉTÉ d'un couple de registres, dont le défaut
  est un ÉCART CALCULABLE, porté dans un état de rapprochement.

  ANCRAGE (D-ED-5) : LE COUPLE BANQUE / CLIENT
  --------------------------------------------
  Richard J., Bensadon D. & Rambaud A., *Comptabilité financière*, 11ᵉ éd.,
  Dunod, 2018, ch. 40, section 4 « État de rapprochement bancaire »,
  p. 639-640 [VÉRIFIÉ — texte lu sur le PDF, pagination des en-têtes] :
    « Chaque entreprise tient son compte Banque (le compte 512). Par
      ailleurs la banque de l'entreprise tient aussi le compte bancaire de
      son client. Normalement ces deux comptes devraient avoir des soldes
      égaux (ils enregistrent les mêmes opérations) et opposés (par exemple
      l'accord par la banque d'un découvert bancaire constitue une rentrée
      de fonds pour l'entreprise et une sortie de fonds pour la banque). »
    « En fait, à un moment donné, il est très rare que le compte bancaire
      tenu par l'entreprise soit égal au solde du relevé […] À la clôture de
      l'exercice chaque entreprise doit : faire un état de rapprochement
      […] montrant : les opérations manquantes sur le relevé de compte
      bancaire mais comptabilisées sur le compte banque (512) de
      l'entreprise ; les opérations manquantes sur le compte banque (512)
      de l'entreprise mais comptabilisées sur le relevé de compte
      bancaire ; enregistrer dans le compte bancaire de l'entreprise (512)
      les opérations figurant sur le relevé bancaire et manquantes sur le
      compte 512. »
  Les trois propriétés y sont : (i) deux teneurs ; (ii) « opposés » ;
  (iii) écart « très rare[ment] » nul, traité par un état de rapprochement.

  Appuis complémentaires, déjà dans le corpus : Carruthers 2017, p. 75-77,
  cité par Chiapello & Violle 2025 (Annexe §A.11) — « le crédit, lui, l'est
  toujours [marqué], car il implique un prêteur et un emprunteur
  particuliers » ; note du porteur du 27/08/2024 (CR 2024-S35) — le contrat
  de crédit « génère une dette à l'actif de la banque et un passif pour
  l'emprunteur. Quand ce contrat est honoré, le passif et l'actif sont
  détruits ».

  RESTE DE TRADUCTION (ce que le modèle perd par rapport à la source)
  -------------------------------------------------------------------
  1. La source exige des soldes ÉGAUX, dans une même unité (l'euro).
     `EcritureDuale` n'exige que l'existence et le sens opposé ; l'égalité
     des montants est un renforcement séparé (`Concordante`). Entre
     registres de communalité aux valorimètres différents, la concordance
     de valeur n'est pas requise (même garde que CONV-10).
  2. La source fait porter le rapprochement par UN SEUL côté (l'entreprise
     complète son 512 d'après le relevé ; les opérations absentes du relevé
     restent en suspens). `completer` modélise ce geste, et
     `le_rapprochement_ne_resorbe_qu_un_sens` en garde la portée.
  3. La source suppose que la banque ADRESSE un relevé. Entre registres de
     communalité, rien ne garantit que B communique le sien. Si B est un
     milieu, son registre est tenu par un écrivant désigné par la
     déclaration des concernés (AX-7) et porte le maintien (CONV-11) :
     `PR37_RegistreDuMilieu.lean` (D-ED-9, 29/09/2026). La communication du
     registre : statut de l'écart selon la communication, PR-40 ; miroir
     reconstitué, PR-45 ; la communication reste NON GARANTIE [D-ED-37 — 30/09/2026].
  4. Le décalage temporel (chèques en circulation) est réduit à la présence
     ou l'absence d'une ligne : aucune date n'est modélisée.

  CE QUE CE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne raccorde pas N2 au registre comptable augmenté (N3, L2) : c'est
    l'objet de `PR36_RaccordAugmenteDuale.lean` (D-ED-8, 29/09/2026), qui
    indexe L2 par son teneur et démontre `raccord_augmente_duale`.
  · Il n'établit pas que la réconciliation des comptes réciproques
    intragroupe (consolidation) a la même forme : vérifiée le 30/09
    (D-ED-10, PR-38) [D-ED-37 — 30/09/2026].

  Identités codées par `Nat` (règle des deux portes, cf. PR-31 : pas de
  `String`, dont la comparaison tire `Classical.choice`).
-/

import ProfReg.PR20_MiroirInterActeurs

namespace ProfRegPR35

open ProfRegPR20 (TypageIA miroirIA miroirIA_involutive Role roleDeTypage)

/-- Une entité teneuse de registre (banque, emprunteur, collectivité…). -/
abbrev Entite := Nat

/-- Une ligne de registre : la contrepartie NOMMÉE (Carruthers : le crédit
    nomme toujours un prêteur et un emprunteur), le typage, un montant
    exprimé dans le valorimètre du registre. -/
structure Ligne (V : Type) where
  contrepartie : Entite
  typage       : TypageIA
  montant      : V
  deriving DecidableEq, Repr

/-- **Propriété (i).** Un registre a un TENEUR. C'est la primitive qui
    manquait au set : jusqu'ici tout registre était une relation globale. -/
structure Registre (V : Type) where
  teneur : Entite
  lignes : List (Ligne V)
  deriving Repr

variable {V : Type}

/-- `m` est le miroir de `l` écrite par le teneur `a` : `m` nomme `a`
    comme contrepartie, et porte le typage miroir. Le montant n'entre pas. -/
def estMiroir (a : Entite) (l m : Ligne V) : Bool :=
  m.contrepartie == a && m.typage == miroirIA l.typage

/-- La ligne `l` de `R` a son miroir dans `R'`. -/
def aSonMiroir (R R' : Registre V) (l : Ligne V) : Bool :=
  R'.lignes.any (estMiroir R.teneur l)

/-- Les lignes que `R` inscrit envers le teneur de `R'`. -/
def lignesVers (R R' : Registre V) : List (Ligne V) :=
  R.lignes.filter (fun l => l.contrepartie == R'.teneur)

/-- **L'écart** : ce que `R` inscrit envers `R'` et que `R'` ne porte pas
    en miroir. C'est une colonne de l'état de rapprochement. -/
def ecart (R R' : Registre V) : List (Ligne V) :=
  (lignesVers R R').filter (fun l => !aSonMiroir R R' l)

/-- **L'état de rapprochement** : les deux colonnes de Richard et al.
    (« manquantes sur le relevé » / « manquantes sur le compte 512 »). -/
def etatRapprochement (RA RB : Registre V) : List (Ligne V) × List (Ligne V) :=
  (ecart RA RB, ecart RB RA)

/-- **L'écriture duale (N2).** Tout ce que A inscrit envers B, B l'inscrit
    envers A avec le typage miroir — « et réciproquement ». -/
def EcritureDuale (RA RB : Registre V) : Prop :=
  ecart RA RB = [] ∧ ecart RB RA = []

/-- **Propriété (iii), versant « contrôlable ».** L'écriture duale est
    décidable sur des registres finis : l'audit du CR S09 (« vérifier que
    les enregistrements duaux ont bien été effectués ») est exécutable. -/
instance [DecidableEq V] (RA RB : Registre V) : Decidable (EcritureDuale RA RB) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## 0. Deux lemmes de liste, prouvés sans `Classical.choice`

`List.filter_eq_nil_iff` de la bibliothèque standard tire `Classical.choice`.
Le contrôle du set (NT-ARCH §8 : toute croissance du nombre de théorèmes
classiques doit être voulue) conduit à le redémontrer constructivement. -/

theorem filtre_vide_de_tous_faux {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, p x = false) → xs.filter p = []
  | [], _ => rfl
  | x :: xs, h => by
    have hx : p x = false := h x (List.mem_cons_self ..)
    rw [List.filter_cons, hx]
    exact filtre_vide_de_tous_faux p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem tous_faux_de_filtre_vide {α : Type} (p : α → Bool) :
    ∀ (xs : List α), xs.filter p = [] → ∀ x ∈ xs, p x = false
  | [], _, _, hm => nomatch hm
  | y :: ys, h, x, hm => by
    rw [List.filter_cons] at h
    cases hy : p y with
    | true => rw [hy] at h; exact nomatch h
    | false =>
      rw [hy] at h
      cases hm with
      | head => exact hy
      | tail _ hm' => exact tous_faux_de_filtre_vide p ys h x hm'

/-! ## 1. L'écriture duale est exactement un état de rapprochement vide -/

/-- Lecture de la définition (R-3) — licite parce que `EcritureDuale`
    discrimine : voir `ecriture_duale_temoin_discriminant`. -/
theorem ecriture_duale_ssi_rapprochement_vide (RA RB : Registre V) :
    EcritureDuale RA RB ↔ etatRapprochement RA RB = ([], []) := by
  unfold EcritureDuale etatRapprochement
  constructor
  · rintro ⟨h1, h2⟩; rw [h1, h2]
  · intro h; exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- « Et réciproquement » : la relation est symétrique entre les deux
    teneurs. `[DÉCLARÉ]` Symétrie par construction de la définition, qui
    exige les deux sens — ce n'est pas un résultat sur le monde. -/
theorem ecriture_duale_symetrique (RA RB : Registre V) :
    EcritureDuale RA RB → EcritureDuale RB RA :=
  fun h => ⟨h.2, h.1⟩

/-! ## 2. Propriété (ii) — le miroir change toujours de rôle -/

/-- Le typage miroir ne porte jamais le rôle de l'original :
    débit chez l'un, crédit chez l'autre. -/
theorem le_miroir_change_de_role (t : TypageIA) :
    roleDeTypage (miroirIA t) ≠ roleDeTypage t := by
  cases t <;> decide

/-- Toute ligne portée en miroir l'est avec le rôle opposé : si `m` est le
    miroir de `l`, créancier et débiteur sont échangés (« soldes […]
    opposés »). -/
theorem la_ligne_miroir_est_de_role_oppose (a : Entite) (l m : Ligne V)
    (h : estMiroir a l m = true) :
    m.contrepartie = a ∧ roleDeTypage m.typage ≠ roleDeTypage l.typage := by
  unfold estMiroir at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, by rw [h.2]; exact le_miroir_change_de_role l.typage⟩

/-! ## 3. L'instance banque / emprunteur (Richard et al. 2018, ch. 40 §4) -/

/-- Teneurs. -/
def banque : Entite := 0
def emprunteur : Entite := 1

/-- Octroi d'un crédit de 100 : la banque inscrit une créance NÉE sur
    l'emprunteur (`C+`), l'emprunteur une dette NÉE envers la banque (`D+`).
    — « une dette à l'actif de la banque et un passif pour l'emprunteur »
    (note du porteur, CR 2024-S35). -/
def registreBanque : Registre Nat :=
  ⟨banque, [⟨emprunteur, .Cplus, 100⟩]⟩

def registreEmprunteur : Registre Nat :=
  ⟨emprunteur, [⟨banque, .Dplus, 100⟩]⟩

/-- **PR-35 (1) — le prêt bancaire est une écriture duale.** -/
theorem pret_bancaire_est_une_ecriture_duale :
    EcritureDuale registreBanque registreEmprunteur := by
  decide

/-- Remboursement vu par la banque seulement : la banque a inscrit
    l'extinction (`C−`), l'emprunteur pas encore (« les commissions
    prélevées par la banque sont immédiatement débitées par elle alors que
    l'entreprise n'en est avertie que plus tard »). -/
def banqueApresRemboursement : Registre Nat :=
  ⟨banque, [⟨emprunteur, .Cplus, 100⟩, ⟨emprunteur, .Cmoins, 100⟩]⟩

/-- **PR-35 (2) — propriété (iii), versant « peut échouer ».** L'écart
    n'est pas vide en général : un couple de registres réels n'est pas en
    écriture duale à tout instant. Contre `lien_est_symetrique` (PR-20),
    où la symétrie est acquise par définition. -/
theorem l_ecriture_duale_peut_echouer :
    ¬ EcritureDuale banqueApresRemboursement registreEmprunteur := by
  decide

/-- Et l'état de rapprochement NOMME ce qui manque : l'extinction inscrite
    par la banque, absente chez l'emprunteur ; rien dans l'autre sens. -/
theorem l_etat_de_rapprochement_nomme_l_ecart :
    etatRapprochement banqueApresRemboursement registreEmprunteur
      = ([⟨emprunteur, .Cmoins, 100⟩], []) := by
  decide

/-! ## 4. Le rapprochement : compléter un registre d'après l'autre -/

/-- Le geste de Richard et al. : « enregistrer dans le compte bancaire de
    l'entreprise (512) les opérations figurant sur le relevé bancaire et
    manquantes ». `completer R' R` ajoute à `R'` le miroir de chaque ligne
    de l'écart de `R` envers `R'`, au même montant. -/
def completer (R' R : Registre V) : Registre V :=
  { R' with lignes := R'.lignes ++
      (ecart R R').map (fun l => ⟨R.teneur, miroirIA l.typage, l.montant⟩) }

/-- **PR-35 (3) — le rapprochement résorbe l'écart dans le sens traité.**
    Après `completer`, plus aucune ligne de `R` envers `R'` n'est sans
    miroir. -/
theorem le_rapprochement_resorbe_l_ecart (R R' : Registre V) :
    ecart R (completer R' R) = [] := by
  unfold ecart
  apply filtre_vide_de_tous_faux
  intro l hl
  have h : aSonMiroir R (completer R' R) l = true := by
    unfold lignesVers at hl
    rw [List.mem_filter] at hl
    have hcp : (l.contrepartie == R'.teneur) = true := hl.2
    unfold aSonMiroir completer
    rw [List.any_append]
    cases hm : aSonMiroir R R' l with
    | true =>
      unfold aSonMiroir at hm
      rw [hm, Bool.true_or]
    | false =>
      have hmem : (⟨R.teneur, miroirIA l.typage, l.montant⟩ : Ligne V) ∈
          (ecart R R').map (fun l => ⟨R.teneur, miroirIA l.typage, l.montant⟩) :=
        List.mem_map.mpr ⟨l, List.mem_filter.mpr
          ⟨List.mem_filter.mpr ⟨hl.1, hcp⟩, by rw [hm]; rfl⟩, rfl⟩
      have hmir : estMiroir R.teneur l ⟨R.teneur, miroirIA l.typage, l.montant⟩ = true := by
        show (R.teneur == R.teneur && miroirIA l.typage == miroirIA l.typage) = true
        -- `decide_eq_true rfl` plutôt que `beq_self_eq_true` : l'instance `LawfulBEq Nat`
        -- de la bibliothèque tire `Classical.choice`.
        rw [show (R.teneur == R.teneur) = true from decide_eq_true rfl, beq_self_eq_true]; rfl
      rw [(List.any_eq_true (p := estMiroir R.teneur l)).mpr ⟨_, hmem, hmir⟩, Bool.or_true]
  rw [h]; rfl

/-- **Garde — le rapprochement ne résorbe qu'un sens.** Le teneur qui
    complète son registre ne complète pas celui de l'autre : les opérations
    « manquantes sur le relevé » restent en suspens. Témoin : l'emprunteur
    inscrit une commission que la banque n'a pas ; la banque inscrit une
    extinction que l'emprunteur n'a pas. L'emprunteur complète son registre
    d'après celui de la banque ; l'écart inverse demeure. -/
def banqueC : Registre Nat := ⟨banque, [⟨emprunteur, .Cmoins, 100⟩]⟩
def emprunteurC : Registre Nat := ⟨emprunteur, [⟨banque, .Dplus, 3⟩]⟩

theorem le_rapprochement_ne_resorbe_qu_un_sens :
    ecart banqueC (completer emprunteurC banqueC) = []
    ∧ ecart (completer emprunteurC banqueC) banqueC ≠ [] := by
  decide

/-! ## 5. Existence sans valeur — et le renforcement « concordante » -/

/-- **Concordance** : l'écriture duale, plus l'égalité des montants ligne à
    ligne. C'est ce qu'exige la source pour le compte bancaire (« soldes
    égaux »), dans une même unité. -/
def estMiroirConcordant [DecidableEq V] (a : Entite) (l m : Ligne V) : Bool :=
  estMiroir a l m && m.montant == l.montant

def ecartConcordant [DecidableEq V] (R R' : Registre V) : List (Ligne V) :=
  (lignesVers R R').filter (fun l => !R'.lignes.any (estMiroirConcordant R.teneur l))

def Concordante [DecidableEq V] (RA RB : Registre V) : Prop :=
  ecartConcordant RA RB = [] ∧ ecartConcordant RB RA = []

instance [DecidableEq V] (RA RB : Registre V) : Decidable (Concordante RA RB) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Le prêt bancaire est concordant : même montant des deux côtés. -/
theorem pret_bancaire_concordant :
    Concordante registreBanque registreEmprunteur := by
  decide

/-- **PR-35 (4) — existence sans valeur.** Deux registres peuvent être en
    écriture duale sans que les montants concordent : l'accord porte sur
    l'existence et le sens, non sur la valeur. Analogue N2 de
    `registre_augmente_non_equivalence` (L2) et de CONV-10. -/
def banqueV : Registre Nat := ⟨banque, [⟨emprunteur, .Cplus, 100⟩]⟩
def emprunteurV : Registre Nat := ⟨emprunteur, [⟨banque, .Dplus, 97⟩]⟩

theorem duale_n_implique_pas_concordante :
    EcritureDuale banqueV emprunteurV ∧ ¬ Concordante banqueV emprunteurV := by
  decide

/-- La concordance implique l'écriture duale. -/
theorem concordante_implique_duale [DecidableEq V] (RA RB : Registre V)
    (h : Concordante RA RB) : EcritureDuale RA RB := by
  have key : ∀ (R R' : Registre V), ecartConcordant R R' = [] → ecart R R' = [] := by
    intro R R' hc
    apply filtre_vide_de_tous_faux
    intro l hl
    have hf := tous_faux_de_filtre_vide _ _ hc l hl
    have hc' : R'.lignes.any (estMiroirConcordant R.teneur l) = true := by
      cases hq : R'.lignes.any (estMiroirConcordant R.teneur l) with
      | true => rfl
      | false => rw [hq] at hf; exact nomatch hf
    obtain ⟨m, hm, hmc⟩ := List.any_eq_true.mp hc'
    have hmir : estMiroir R.teneur l m = true := by
      unfold estMiroirConcordant at hmc
      cases he : estMiroir R.teneur l m with
      | true => rfl
      | false => rw [he, Bool.false_and] at hmc; exact nomatch hmc
    have ha : aSonMiroir R R' l = true := List.any_eq_true.mpr ⟨m, hm, hmir⟩
    rw [ha]; rfl
  exact ⟨key RA RB h.1, key RB RA h.2⟩

/-! ## 6. Témoins discriminants (règle R-7) -/

/-- `EcritureDuale` discrimine : vraie sur le prêt, fausse après une
    extinction inscrite d'un seul côté. -/
theorem ecriture_duale_temoin_discriminant :
    EcritureDuale registreBanque registreEmprunteur
    ∧ ¬ EcritureDuale banqueApresRemboursement registreEmprunteur :=
  ⟨pret_bancaire_est_une_ecriture_duale, l_ecriture_duale_peut_echouer⟩

/-- Un registre vide envers l'autre est trivialement en écriture duale :
    l'écriture duale ne dit rien de ce qui n'a été inscrit par personne.
    `[GARDE]` Une absence d'inscription des deux côtés n'est pas un accord
    — même leçon que `absence_n_est_pas_lien_nul` (PR-20). -/
theorem deux_silences_sont_en_ecriture_duale :
    EcritureDuale (⟨banque, []⟩ : Registre Nat) ⟨emprunteur, []⟩ := by
  decide

end ProfRegPR35
