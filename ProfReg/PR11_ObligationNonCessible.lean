/-
  PR-11 · `obligation_non_cessible`
  =================================

  **Appui formel du nœud NC** (non-cessibilité), condition d'existence
  du palier **PAL-6′** — marquage à la primo-affectation, décidé le
  7 septembre 2026 (`P6_prime_Marquage_Primo-affectation_2026-09-07.md`).

  L'ÉNONCÉ DU SET, MOT POUR MOT
  -----------------------------
  > « **Non-cessibilité.** L'obligation inscrite n'est pas transférable.
  >   Aucune transition du registre ne substitue un porteur à un autre.
  >   L'extinction d'une obligation est conditionnée à la réalisation
  >   vérifiée, jamais au transfert. »

  [D-9a, 28/09/2026 — décision de porteur] **Portée bornée.** NC porte sur
  l'extinction **par exécution** : elle est conditionnée à la réalisation
  vérifiée, **jamais au transfert**. Les autres modes d'extinction admis
  depuis le 21/09 — remise, prescription, disparition de l'objet — relèvent
  du **second axe** (NT-ARCH §4bis) et de ses exigences (interprète nommé,
  écriture appariée) ; ils sont **hors du modèle** de ce fichier. Le cœur de
  NC, « jamais par transfert », n'est pas touché.

  Fondement : **AX-2** — une obligation soldable par transfert n'est pas
  une obligation. Et la raison opératoire : *une écriture porteuse de
  valeur et cessible est un crédit carbone.*

  POURQUOI CE FICHIER EST ÉCRIT ALORS QUE L'ARBITRAGE N'EST PAS PRIS
  ------------------------------------------------------------------
  Le set posait un préalable : *« la frontière entre cession (interdite)
  et dévolution — que devient l'obligation quand son porteur disparaît,
  faillite ou dissolution ? Sans règle, PR-11 rend les obligations
  inexécutables à la première liquidation. »*

  **Ce fichier ne tranche pas ce préalable : il le paramètre**, comme
  PR-3 a été écrit en option C (paramétré par l'échéance de
  déclaration, le régime strict démontré comme instance du repli). Le
  `RegimeDevolution` est un paramètre ; les théorèmes disent ce qui vaut
  **pour tout régime**, et ce que chaque régime coûte.

  CE QUE LE FICHIER ÉTABLIT, ET QUI N'ÉTAIT PAS PRÉVU
  ---------------------------------------------------
  · §2 La **non-cessibilité ne dépend d'aucun régime de dévolution** :
    le transfert est refusé pour tout régime. **L'arbitrage à venir ne
    peut donc pas affaiblir NC** — c'est la garantie que le porteur
    n'avait pas.

  · §4 **L'effet ne distingue pas la cession de la dévolution.** On
    exhibe un transfert refusé et une dévolution admise qui produisent
    **exactement la même obligation**. La frontière n'est donc pas dans
    le résultat : elle est dans **l'événement**. Conséquence directe
    pour le registre : il doit inscrire l'**événement**, pas seulement
    l'état.

  · §5 **Une dévolution à successeur libre reconstitue la cession.**
    D'où : le régime doit être **déclaré et figé à l'inscription**.
    C'est la moitié du préalable que la formalisation tranche seule.

  `[RÉSERVE DE MODÈLE]` `Obligation`, `Evenement` et `appliquer` sont
  mes structures. Réserve du §2quinquies du graphe : un contre-exemple
  ne vaut que ce que vaut la fidélité de son modèle.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib, sans import.
-/

namespace ProfRegPR11

/-! ## 1. Le modèle

Une obligation porte **qui la doit** et **où elle en est**. Le registre
la fait évoluer par des **événements**, et c'est la fonction de
transition qui porte la contrainte — patron de `transition_valide`
(V4), où les interdictions sont encodées dans la définition. -/

/-- L'état d'une obligation. `realisee` est le seul état d'extinction
    **du modèle**, et il n'est atteint que par réalisation vérifiée (§3).
    [D-9a, 28/09] Le modèle ne connaît que l'extinction par exécution ;
    remise et prescription relèvent du second axe (NT-ARCH §4bis). -/
inductive StatutObl where
  | inscrite
  | realisee
  deriving DecidableEq, Repr

structure Obligation (A : Type) where
  porteur : A
  statut  : StatutObl
  deriving Repr

/-- Ce qui peut arriver à une obligation.

    La distinction qui compte n'est pas dans l'effet mais dans **qui
    déclenche** : le `transfert` est **choisi** par le porteur, la
    `disparitionDuPorteur` est **subie**. §4 démontre que le registre ne
    peut pas les distinguer autrement. -/
inductive Evenement (A : Type) where
  | realisationVerifiee
  | transfert (nouveauPorteur : A)
  | disparitionDuPorteur

/-- **Le paramètre de l'arbitrage non pris.** Le successeur déclaré pour
    chaque porteur — `none` signifiant : pas de dévolution prévue pour
    lui.

    Ce champ **est une fonction du porteur, pas de l'instant** : c'est
    ce qui distingue un régime déclaré d'un choix fait au moment de la
    disparition, et §5 montre que la distinction n'est pas décorative. -/
structure RegimeDevolution (A : Type) where
  successeur : A → Option A

/-- Le régime **strict** : aucune dévolution, jamais. C'est la lecture
    littérale de NC, et §6 en montre le coût. -/
def stricte (A : Type) : RegimeDevolution A := ⟨fun _ => none⟩

/-- **La fonction de transition du registre.** `none` = l'événement est
    refusé, aucune écriture n'est produite.

    La deuxième ligne **est** la non-cessibilité : elle ne consulte pas
    le régime, elle refuse. -/
def appliquer {A : Type} (r : RegimeDevolution A) (o : Obligation A) :
    Evenement A → Option (Obligation A)
  | Evenement.realisationVerifiee  => some { o with statut := StatutObl.realisee }
  | Evenement.transfert _          => none
  | Evenement.disparitionDuPorteur =>
      match r.successeur o.porteur with
      | some s => some { o with porteur := s }
      | none   => none

variable {A : Type}

/-! ## 2. PR-11 — la non-cessibilité, et elle ne dépend d'aucun régime -/

/-- **PR-11.** Aucun transfert n'est admis — **pour tout régime de
    dévolution, toute obligation et tout candidat porteur**.

    C'est la forme forte de l'énoncé du set, et le point important est
    la quantification sur `r` : **l'arbitrage sur la dévolution, quel
    qu'il soit, ne peut pas affaiblir la non-cessibilité.** -/
theorem obligation_non_cessible (r : RegimeDevolution A) (o : Obligation A)
    (b : A) : appliquer r o (Evenement.transfert b) = none := rfl

/-- **Et aucune transition admise ne substitue un porteur à un autre**,
    hors du seul cas de dévolution. C'est la phrase du set — « aucune
    transition du registre ne substitue un porteur à un autre » — dans
    sa portée exacte. -/
theorem porteur_stable_hors_devolution (r : RegimeDevolution A)
    (o o' : Obligation A) (e : Evenement A)
    (h : appliquer r o e = some o')
    (hne : ∀ x, e ≠ Evenement.transfert x) :
    e = Evenement.disparitionDuPorteur ∨ o'.porteur = o.porteur := by
  cases e with
  | realisationVerifiee =>
      exact Or.inr (congrArg Obligation.porteur (Option.some.inj h)).symm
  | transfert x => exact absurd rfl (hne x)
  | disparitionDuPorteur => exact Or.inl rfl

/-! ## 3. L'extinction n'est atteinte que par la réalisation vérifiée -/

/-- **PR-11 (2).** Si une obligation non encore éteinte devient éteinte,
    l'événement était la **réalisation vérifiée**. Ni le transfert (il
    est refusé) ni la dévolution (elle ne touche pas au statut) ne
    peuvent éteindre.

    C'est la seconde moitié de l'énoncé du set : *« l'extinction est
    conditionnée à la réalisation vérifiée, jamais au transfert »*.

    [D-9a, 28/09/2026] **Portée : l'extinction par exécution.** Parmi les
    trois événements du modèle, seule la réalisation vérifiée éteint. Le
    théorème ne dit rien de la remise ni de la prescription, que le modèle
    ne contient pas et que le second axe admet (NT-ARCH §4bis.2). Ce qu'il
    établit pour tout mode : **le transfert n'éteint jamais**. -/
theorem seule_la_realisation_eteint (r : RegimeDevolution A)
    (o o' : Obligation A) (e : Evenement A)
    (h : appliquer r o e = some o')
    (ho : o.statut ≠ StatutObl.realisee)
    (h' : o'.statut = StatutObl.realisee) :
    e = Evenement.realisationVerifiee := by
  cases e with
  | realisationVerifiee => rfl
  | transfert x => exact absurd h (by simp [appliquer])
  | disparitionDuPorteur =>
      exfalso
      simp only [appliquer] at h
      cases hs : r.successeur o.porteur with
      | none => rw [hs] at h; simp at h
      | some s =>
          rw [hs] at h
          have hoo : o' = { o with porteur := s } := (Option.some.inj h).symm
          rw [hoo] at h'
          exact ho h'

/-- **Et la dévolution ne solde rien.** Une obligation qui change de
    porteur garde son statut : le transfert de charge n'est pas une
    exécution. C'est AX-2 à l'échelle de la transition. -/
theorem la_devolution_ne_solde_pas (r : RegimeDevolution A)
    (o o' : Obligation A)
    (h : appliquer r o Evenement.disparitionDuPorteur = some o') :
    o'.statut = o.statut := by
  simp only [appliquer] at h
  cases hs : r.successeur o.porteur with
  | none => rw [hs] at h; simp at h
  | some s =>
      rw [hs] at h
      exact (congrArg Obligation.statut (Option.some.inj h)).symm

/-! ## 4. Le résultat qui n'était pas prévu — l'effet ne distingue pas

C'est le contenu propre du fichier, et il porte directement sur
l'arbitrage à prendre. -/

/-- **PR-11 (3).** Il existe un transfert **refusé** et une dévolution
    **admise** qui produisent **exactement la même obligation**.

    La frontière entre cession et dévolution n'est donc **pas dans le
    résultat**. Deux registres qui n'inscriraient que l'état seraient
    indiscernables. **Elle est dans l'événement** — c'est-à-dire dans ce
    qui a déclenché la transition, et que seul le registre peut inscrire.

    *Conséquence directe pour le modèle : le registre doit inscrire
    l'événement, pas seulement l'état.* -/
theorem l_effet_ne_distingue_pas_cession_et_devolution (a b : A) (st : StatutObl) :
    ∃ (r : RegimeDevolution A) (o : Obligation A),
      o.porteur = a
      ∧ appliquer r o (Evenement.transfert b) = none
      ∧ appliquer r o Evenement.disparitionDuPorteur
          = some { porteur := b, statut := st } := by
  exact ⟨⟨fun _ => some b⟩, ⟨a, st⟩, rfl, rfl, rfl⟩

/-- **Et l'état résultant efface son origine.** Deux obligations portées
    par des porteurs **différents** produisent, après dévolution vers le
    même successeur, **exactement la même obligation** : rien dans
    l'état ne dit de qui la charge vient.

    Ce n'est pas anodin pour la lecture de R-PRIORITE-CREANCIERS : si le
    registre n'inscrit que l'état, la chaîne des porteurs successifs est
    perdue. **Second motif, indépendant du §4, d'inscrire l'événement.** -/
theorem l_etat_efface_son_origine (a₁ a₂ b : A) (st : StatutObl) :
    appliquer ⟨fun _ => some b⟩ ⟨a₁, st⟩ Evenement.disparitionDuPorteur
      = appliquer ⟨fun _ => some b⟩ ⟨a₂, st⟩ Evenement.disparitionDuPorteur := rfl

/-! ## 5. Une dévolution à successeur libre reconstitue la cession

Et c'est la moitié du préalable que la formalisation tranche seule. -/

/-- **PR-11 (4).** Pour **tout** couple de porteurs `a`, `b`, il existe
    un régime de dévolution sous lequel l'obligation de `a` échoit
    à `b`.

    Autrement dit : si le successeur pouvait être choisi **au moment de
    la disparition**, la dévolution reconstituerait exactement la
    cession que §2 interdit. **Le régime doit donc être déclaré et figé
    à l'inscription** — sans quoi l'interdiction du transfert est sans
    portée. -/
theorem devolution_libre_reconstitue_la_cession (a b : A) (st : StatutObl) :
    ∃ r : RegimeDevolution A,
      appliquer r ⟨a, st⟩ Evenement.disparitionDuPorteur = some ⟨b, st⟩ :=
  ⟨⟨fun _ => some b⟩, rfl⟩

/-- **Le résultat dépend du régime**, donc le régime est une donnée de
    l'inscription et non une circonstance : sur la même obligation et le
    même événement, deux régimes donnent deux issues différentes — l'une
    refuse, l'autre transfère. -/
theorem le_resultat_depend_du_regime (a b : A) (st : StatutObl) :
    ∃ r₁ r₂ : RegimeDevolution A,
      appliquer r₁ ⟨a, st⟩ Evenement.disparitionDuPorteur
        ≠ appliquer r₂ ⟨a, st⟩ Evenement.disparitionDuPorteur := by
  refine ⟨stricte A, ⟨fun _ => some b⟩, ?_⟩
  intro h
  simp [appliquer, stricte] at h

/-! ## 6. Le coût du régime strict — l'obligation devient inexécutable

Le set le déclarait en lacune ; il est ici démontré. -/

/-- **PR-11 (5).** Sous le régime strict, la disparition du porteur est
    **refusée** : aucune écriture n'est produite, et l'obligation reste
    attachée à un porteur qui n'existe plus.

    C'est exactement la contrepartie que le set avait déclarée sans
    l'instruire : *« une obligation non cessible peut devenir
    inexécutable si son porteur disparaît »*. **Elle n'est plus une
    crainte : c'est une propriété du régime strict.** -/
theorem regime_strict_bloque_a_la_disparition (o : Obligation A) :
    appliquer (stricte A) o Evenement.disparitionDuPorteur = none := rfl

/-- **Et le blocage est définitif pour ce porteur** : sous le régime
    strict, aucune suite d'événements ne change le porteur, puisque le
    transfert est refusé et la dévolution aussi. Le seul événement
    encore admis est la réalisation — que personne ne peut plus
    accomplir.

    On l'écrit sous la forme décidable : tout événement admis sous le
    régime strict laisse le porteur inchangé. -/
theorem regime_strict_fige_le_porteur (o o' : Obligation A) (e : Evenement A)
    (h : appliquer (stricte A) o e = some o') : o'.porteur = o.porteur := by
  cases e with
  | realisationVerifiee =>
      exact (congrArg Obligation.porteur (Option.some.inj h)).symm
  | transfert x => simp [appliquer] at h
  | disparitionDuPorteur => simp [appliquer, stricte] at h

/-! ## 7. Gardes -/

/-- **PR-11 n'interdit pas la dévolution.** Il interdit le transfert.
    Un régime à successeur déclaré admet la disparition du porteur, et
    la non-cessibilité y tient toujours (§2, quantifié sur `r`).
    **L'arbitrage reste entier, et il est sans risque pour NC.** -/
theorem PR11_n_interdit_pas_la_devolution (a b : A) (st : StatutObl) :
    ∃ r : RegimeDevolution A,
      (appliquer r ⟨a, st⟩ Evenement.disparitionDuPorteur ≠ none)
      ∧ (∀ x, appliquer r ⟨a, st⟩ (Evenement.transfert x) = none) := by
  refine ⟨⟨fun _ => some b⟩, ?_, fun _ => rfl⟩
  intro h
  simp [appliquer] at h

/-- **PR-11 ne choisit pas le régime.** Deux régimes opposés — strict et
    à successeur déclaré — satisfont l'un et l'autre la non-cessibilité.
    Patron de `PR3_ne_choisit_pas_le_regime`. -/
theorem PR11_ne_choisit_pas_le_regime (b : A) :
    (∀ (o : Obligation A) (x : A),
        appliquer (stricte A) o (Evenement.transfert x) = none)
  ∧ (∀ (o : Obligation A) (x : A),
        appliquer ⟨fun _ => some b⟩ o (Evenement.transfert x) = none) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **PR-11 ne vérifie pas la réalisation.** L'événement
    `realisationVerifiee` est admis sur **toute** obligation : le
    théorème dit que l'extinction passe par lui, il ne dit pas que ce
    qu'il nomme a eu lieu. **La vérification est ailleurs** — et c'est
    exactement ce que PAL-6′ met à la charge des tiers. -/
theorem PR11_ne_verifie_pas_la_realisation (r : RegimeDevolution A)
    (o : Obligation A) :
    appliquer r o Evenement.realisationVerifiee
      = some { o with statut := StatutObl.realisee } := rfl

/-- **PR-11 ne dit rien du bien-fondé de l'obligation.** Deux
    obligations de porteurs différents se comportent identiquement sous
    la transition : le fichier porte sur la circulation de la charge,
    jamais sur sa justesse. -/
theorem PR11_ne_juge_pas_l_obligation (a b : A) (st : StatutObl) (x : A) :
    appliquer (stricte A) ⟨a, st⟩ (Evenement.transfert x)
      = appliquer (stricte A) ⟨b, st⟩ (Evenement.transfert x) := rfl

end ProfRegPR11
