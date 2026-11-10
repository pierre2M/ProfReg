import ProfReg.PR34_InstrumentHote

/-
  PR-54 · `boucle_confirmante_détectée` et contre-performativité (NT-G4 §2.1, §8 ;
  NT-ARCH F3 §3.3, §3.5, §B.2bis.6)
  ==============================================================================

  NT-G4 déclare une `[LACUNE D'INSTRUMENT]` : le signal `boucle_confirmante_détectée`
  ne voit que le **point fixe** — le cas où l'effet de l'instrument est aligné sur
  l'intention — et reste aveugle au cas où l'effet va **contre** l'intention. Ce
  second cas a un nom dans la littérature : la **contre-performativité**,
  « where representational interventions yield effects that undermine or diverge
  from their intended goals » (Unal, Polillo, Caliskan & MacKenzie 2025, *Finance
  and Society*, p. 20 — lecture directe, biblio).

  NT-G4 §8 et NT-ARCH §B.2bis.6 écrivent que l'**effet d'hôte** (P5, PR-34) lève
  cette lacune **en partie** : un cas de désalignement est instrumenté, non leur
  détection générale. Ce fichier donne la **forme** de cette levée partielle :

  · le signal de boucle atteste l'alignement, et seulement lui (§2) ;
  · une boucle contre-performative ne le lève jamais (§2) ;
  · l'effet d'hôte voit un cas contraire (§3) ;
  · hors effet d'hôte, aucun des deux ne voit la contre-performativité (§3) ;
  · les deux signaux lisent des **déclarations**, jamais les faits : un hôte réel
    déclaré `AUCUN` échappe (§4).

  Ce fichier établit une forme, non la fréquence des cas ni la justesse d'une
  déclaration. `[RÉSERVE DE MODÈLE]` `aligne` et `hoteReel` sont des **faits**
  que le registre ne connaît pas : ils servent à énoncer ce que les signaux ne
  lisent pas. La boucle « Mode → M-SEMANTIQUE → Mode » est réduite à un booléen ;
  sa structure catégorielle reste hors ProfReg (NT-ARCH F3 §3.5). Lean 4 pur,
  sans Mathlib ; importe PR-34.

  Porteur : Pierre Musseau. Écrit le 12 octobre 2026.
-/

namespace ProfRegPR54

open ProfRegPR34

/-! ## 1. Le modèle -/

/-- Une écriture, ses déclarations P5 (PR-34) et deux faits non déclarés. -/
structure EcritureP where
  /-- Ce que l'écriture déclare au titre de P5 (opération instituante, hôte). -/
  declaree : EcritureInstituee
  /-- Une boucle Mode → M-SEMANTIQUE → Mode est observée. -/
  boucle : Bool
  /-- Fait : l'effet de l'instrument va dans le sens de l'intention. -/
  aligne : Bool
  /-- Fait : l'inscription est logée dans un dispositif préexistant. -/
  hoteReel : Bool
  deriving DecidableEq, Repr

/-- **`boucle_confirmante_détectée`** : la boucle se referme sur un point fixe
    aligné (NT-ARCH F3 §3.3). -/
def boucleConfirmante (e : EcritureP) : Bool := e.boucle && e.aligne

/-- **Contre-performativité** (Unal et al. 2025, p. 20) : une boucle dont
    l'effet va contre l'intention. -/
def contrePerformative (e : EcritureP) : Bool := e.boucle && !e.aligne

/-- `INSTRUMENT_HOTE_NON_DECLARE` ou marqueur d'hôte incomplet : un défaut P5
    (PR-34, `effetP5`). -/
def signalHote (e : EcritureP) : Bool := (effetP5 e.declaree).isSome

/-- Un hôte déclaré : le désalignement possible est tracé, sans signal. -/
def hoteTrace (e : EcritureP) : Bool :=
  match e.declaree.hote with
  | .declare _ => true
  | _ => false

/-- **Ce que le registre voit** d'un désalignement possible : une boucle
    confirmante, un défaut P5, ou un hôte déclaré. -/
def vue (e : EcritureP) : Bool := boucleConfirmante e || signalHote e || hoteTrace e

/-! ## 2. Le signal de boucle : l'alignement, et lui seul -/

/-- **PR-54 (1) — un signal de boucle atteste un point fixe aligné.** -/
theorem boucle_confirmante_atteste_l_alignement (e : EcritureP)
    (h : boucleConfirmante e = true) : e.boucle = true ∧ e.aligne = true := by
  simpa [boucleConfirmante] using h

/-- **PR-54 (2) — la contre-performativité ne lève jamais le signal de boucle.**
    C'est la `[LACUNE D'INSTRUMENT]` de NT-G4, sous forme de théorème. -/
theorem la_contre_performativite_ne_leve_pas_la_boucle (e : EcritureP)
    (h : contrePerformative e = true) : boucleConfirmante e = false := by
  cases e with
  | mk d b a r => cases b <;> cases a <;> simp_all [contrePerformative, boucleConfirmante]

/-- **Témoin discriminant** : la même écriture, à l'alignement près, lève ou
    non le signal de boucle. -/
theorem boucle_temoin_discriminant :
    boucleConfirmante ⟨⟨.aucune, .aucun, false⟩, true, true, false⟩ = true
  ∧ boucleConfirmante ⟨⟨.aucune, .aucun, false⟩, true, false, false⟩ = false := ⟨rfl, rfl⟩

/-! ## 3. L'effet d'hôte : une levée partielle -/

/-- **PR-54 (3) — l'effet d'hôte voit un cas contraire.** Une écriture
    contre-performative, logée dans un hôte, sous `INSTRUMENTATION` sans hôte
    renseigné : le défaut P5 se lève (E3, PR-34). -/
theorem l_effet_d_hote_voit_un_cas_contraire :
    ∃ e : EcritureP, contrePerformative e = true ∧ e.hoteReel = true ∧ signalHote e = true :=
  ⟨⟨⟨.instrumentation, .nonRenseigne, false⟩, true, false, true⟩, rfl, rfl, rfl⟩

/-- **PR-54 (4) — hors effet d'hôte, la contre-performativité n'est vue par
    aucun signal.** Si l'écriture ne déclare ni `INSTRUMENTATION` ni hôte, une
    boucle contre-performative ne laisse aucune trace. C'est la forme exacte de
    « la levée est partielle ». -/
theorem hors_hote_la_contre_performativite_est_invisible (e : EcritureP)
    (hc : contrePerformative e = true)
    (ho : e.declaree.operation ≠ .instrumentation)
    (hh : e.declaree.hote = .aucun ∨ e.declaree.hote = .nonRenseigne) :
    vue e = false := by
  have hb : boucleConfirmante e = false := la_contre_performativite_ne_leve_pas_la_boucle e hc
  have hs : signalHote e = false := by
    simp [signalHote, effetP5, ho]
  have ht : hoteTrace e = false := by
    rcases hh with h | h <;> simp [hoteTrace, h]
  simp [vue, hb, hs, ht]

/-- **Témoin** : un désalignement sans hôte reste invisible. -/
theorem desalignement_sans_hote_temoin :
    ∃ e : EcritureP, contrePerformative e = true ∧ e.hoteReel = false ∧ vue e = false :=
  ⟨⟨⟨.aucune, .aucun, false⟩, true, false, false⟩, rfl, rfl, rfl⟩

/-! ## 4. Les signaux lisent des déclarations -/

/-- **PR-54 (5) — aucun signal ne lit les faits.** Ce que le registre voit ne
    dépend ni de l'alignement réel hors boucle, ni de l'existence réelle d'un
    hôte : changer `hoteReel` ne change rien. « Déclarer n'est pas guérir »
    (NT-ARCH §B.2bis.6) a pour envers : ne pas déclarer, c'est ne pas être vu.
    `[LECTURE — dépliage de `vue`]` Témoin : `un_hote_reel_declare_aucun_echappe`. -/
theorem le_registre_ne_lit_pas_l_hote_reel (e : EcritureP) (b : Bool) :
    vue { e with hoteReel := b } = vue e := rfl

/-- **Témoin** : un hôte réel, déclaré `AUCUN` sous une opération déclarée
    `AUCUNE`, dans une boucle contre-performative, échappe à tout signal. La
    réciproque de §B.2bis.3 (hôte ≠ AUCUN ⇒ opération ≠ AUCUNE) porte sur les
    déclarations : elle ne rattrape pas une fausse déclaration `AUCUN`. -/
theorem un_hote_reel_declare_aucun_echappe :
    ∃ e : EcritureP, e.hoteReel = true ∧ contrePerformative e = true ∧ vue e = false :=
  ⟨⟨⟨.aucune, .aucun, false⟩, true, false, true⟩, rfl, rfl, rfl⟩

end ProfRegPR54
