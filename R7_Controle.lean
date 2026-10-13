import ProfReg
/-!
# Contrôle mécanique de la table nominative R-7 (Consolidé §2.3)

28/09/2026. Pour chaque lecture de fonction licite (n° 1 à 58), un `example`
établit, **à partir de la lecture et de son témoin nommés**, que la fonction lue
rend une **autre valeur** sur l'entrée du témoin — ou, pour les invariances
témoignées (R-7 (iii)), que la fonction **modifie un autre champ**.

Ce fichier n'ajoute aucun théorème au décompte : il ne contient que des
`example`, que Lean vérifie et qu'`Audit.lean` n'audite pas.
Lancer : `lake env lean R7_Controle.lean` — silence = contrôle passé.
-/

section PR11
open ProfRegPR11
variable {A : Type}
-- n° 1, 5
example (r : RegimeDevolution A) (o : Obligation A) (b : A) :
    appliquer r o (Evenement.transfert b) ≠ appliquer r o Evenement.realisationVerifiee := by
  rw [obligation_non_cessible, PR11_ne_verifie_pas_la_realisation]; simp
-- n° 2 (invariance en l'origine ; la fonction dépend du régime)
example (a b : A) (st : StatutObl) :
    ∃ r₁ r₂ : RegimeDevolution A, appliquer r₁ ⟨a, st⟩ Evenement.disparitionDuPorteur
      ≠ appliquer r₂ ⟨a, st⟩ Evenement.disparitionDuPorteur :=
  le_resultat_depend_du_regime a b st
-- n° 3
example (a b : A) (st : StatutObl) :
    ∃ r, appliquer (stricte A) ⟨a, st⟩ Evenement.disparitionDuPorteur
      ≠ appliquer r ⟨a, st⟩ Evenement.disparitionDuPorteur := by
  obtain ⟨r, hr⟩ := devolution_libre_reconstitue_la_cession a b st
  exact ⟨r, by rw [regime_strict_bloque_a_la_disparition, hr]; simp⟩
-- n° 4
example (b x : A) (o : Obligation A) :
    appliquer (stricte A) o (Evenement.transfert x) ≠ appliquer (stricte A) o Evenement.realisationVerifiee := by
  rw [(PR11_ne_choisit_pas_le_regime b).1 o x, PR11_ne_verifie_pas_la_realisation]; simp
-- n° 6
example (a b : A) (st : StatutObl) (h : a ≠ b) :
    appliquer (stricte A) ⟨a, st⟩ Evenement.realisationVerifiee
      ≠ appliquer (stricte A) ⟨b, st⟩ Evenement.realisationVerifiee := by
  rw [PR11_ne_verifie_pas_la_realisation, PR11_ne_verifie_pas_la_realisation]; simp [h]
end PR11

section PR12
open ProfRegPR12
-- n° 7, 9, 14, 16
example (c : ConditionsAvarie) (m : Nat) (h : avarieQualifiee c = true) :
    appliquer ⟨Regime.A2, c, m, true⟩ Traitement.repartir
      ≠ appliquer ⟨Regime.A2, c, m, true⟩ Traitement.renouveler := by
  rw [l_obligation_A2_ne_se_repartit_pas _ rfl]
  exact fun e => (PR12_ne_qualifie_aucune_dette c m h).1 e.symm
example (c : ConditionsAvarie) (m : Nat) (h : avarieQualifiee c = true) :
    appliquer ⟨Regime.A2, c, m, true⟩ Traitement.repartir
      ≠ appliquer ⟨Regime.A2, c, m, true⟩ Traitement.renouveler := by
  rw [(les_deux_erreurs_sont_symetriques ⟨Regime.A2, c, m, true⟩ ⟨Regime.A3, c, m, true⟩ rfl rfl).1]
  exact fun e => (PR12_ne_qualifie_aucune_dette c m h).1 e.symm
example (c : ConditionsAvarie) (m : Nat) (h : avarieQualifiee c = true) :
    appliquer ⟨Regime.A2, c, m, true⟩ Traitement.repartir
      ≠ appliquer ⟨Regime.A3, c, m, true⟩ Traitement.repartir := by
  rw [PR12_ne_hierarchise_pas, la_charge_A3_ne_se_renouvelle_pas _ rfl]
  exact fun e => (PR12_ne_qualifie_aucune_dette c m h).2 e.symm
-- n° 8
example (c : ConditionsAvarie) (m : Nat) (h : avarieQualifiee c = true) :
    appliquer ⟨Regime.A3, c, m, true⟩ Traitement.renouveler
      ≠ appliquer ⟨Regime.A3, c, m, true⟩ Traitement.repartir := by
  rw [la_charge_A3_ne_se_renouvelle_pas _ rfl]
  exact fun e => (PR12_ne_qualifie_aucune_dette c m h).2 e.symm
-- n° 10
example (c : ConditionsAvarie) (m : Nat) (b : Bool) (h : avarieQualifiee c = true) :
    appliquer ⟨Regime.nonDeclare, c, m, b⟩ Traitement.renouveler
      ≠ appliquer ⟨Regime.A2, c, m, true⟩ Traitement.renouveler := by
  rw [regime_non_declare_ne_vaut_pas_permission _ rfl]
  exact fun e => (PR12_ne_qualifie_aucune_dette c m h).1 e.symm
-- n° 11
example (c c' : ConditionsAvarie) (m : Nat) (h : avarieQualifiee c = true) (hr : c'.resultatUtile = false) :
    appliquer ⟨Regime.A3, c', m, true⟩ Traitement.repartir
      ≠ appliquer ⟨Regime.A3, c, m, true⟩ Traitement.repartir := by
  rw [sans_resultat_utile_aucune_repartition ⟨Regime.A3, c', m, true⟩ rfl hr]
  exact fun e => (PR12_ne_qualifie_aucune_dette c m h).2 e.symm
-- n° 12
example (c : ConditionsAvarie) (m : Nat) (h : avarieQualifiee c = true) :
    appliquer ⟨Regime.A3, c, m, false⟩ Traitement.repartir
      ≠ appliquer ⟨Regime.A3, c, m, true⟩ Traitement.repartir := by
  rw [sans_mandat_borne_aucune_repartition ⟨Regime.A3, c, m, false⟩ rfl rfl]
  exact fun e => (PR12_ne_qualifie_aucune_dette c m h).2 e.symm
-- n° 13 (témoin direct du 28/09)
example (c : ConditionsAvarie) (m : Nat) (b : Bool) :
    confusionDesDeuxDettes ⟨Regime.nonDeclare, c, m, b⟩ Traitement.repartir
      ≠ confusionDesDeuxDettes ⟨Regime.A2, c, m, b⟩ Traitement.repartir := by
  rw [(le_silence_n_est_pas_une_confusion ⟨Regime.nonDeclare, c, m, b⟩ Traitement.repartir rfl).1,
      confusion_temoin_discriminant]; decide
-- n° 15
example (c : ConditionsAvarie) (m : Nat) (h : avarieQualifiee c = true) :
    (appliquer ⟨Regime.A2, c, m, true⟩ Traitement.repartir).isSome
      ≠ (appliquer ⟨Regime.A2, c, m, true⟩ Traitement.renouveler).isSome := by
  rw [l_obligation_A2_ne_se_repartit_pas _ rfl]
  have := (PR12_ne_qualifie_aucune_dette c m h).1
  cases hh : appliquer ⟨Regime.A2, c, m, true⟩ Traitement.renouveler <;> simp_all
end PR12

section PR13
open ProfRegPR13
-- n° 17, 18
example (n : Niveau) (c₁ c₂ : Nat) :
    nonEquivalentes ⟨some n, c₁⟩ ⟨some n, c₂⟩ ≠ nonEquivalentes ⟨none, c₁⟩ ⟨some n, c₂⟩ := by
  rw [la_non_equivalence_est_calculee, (sans_niveau_declare_aucun_verdict _ _).1]; simp
-- n° 19, 22
example (n₁ n₂ : Niveau) (c₁ c₂ : Nat) (h : n₁ ≠ n₂) :
    fusionner ⟨some n₁, c₁⟩ ⟨some n₂, c₂⟩ ≠ fusionner ⟨some n₁, c₁⟩ ⟨some n₁, c₂⟩ := by
  rw [aucune_fusion_entre_niveaux_distincts _ _ _ _ h]
  exact fun e => PR13_n_interdit_pas_le_meme_niveau n₁ c₁ c₂ e.symm
-- n° 20
example (n : Niveau) (c₁ c₂ : Nat) :
    fusionner ⟨none, c₁⟩ ⟨some n, c₂⟩ ≠ fusionner ⟨some n, c₁⟩ ⟨some n, c₂⟩ := by
  rw [niveau_non_declare_ne_vaut_pas_permission]
  exact fun e => PR13_n_interdit_pas_le_meme_niveau n c₁ c₂ e.symm
-- n° 21
example (n : Niveau) (c₁ c₂ : Nat) :
    fusionner ⟨some n, c₁⟩ ⟨none, c₂⟩ ≠ fusionner ⟨some n, c₁⟩ ⟨some n, c₂⟩ := by
  rw [niveau_non_declare_a_droite_ne_vaut_pas_permission]
  exact fun e => PR13_n_interdit_pas_le_meme_niveau n c₁ c₂ e.symm
-- n° 23, 24
example (c₁ c₂ : Nat) :
    fusionner ⟨some Niveau.entite, c₁⟩ ⟨some Niveau.territoire, c₂⟩
      ≠ fusionner ⟨some Niveau.entite, c₁⟩ ⟨some Niveau.entite, c₂⟩ := by
  rw [entite_et_territoire_ne_fusionnent_pas, la_fusion_au_meme_niveau_somme_les_charges]; simp
end PR13

section PR19
open ProfRegPR19
-- n° 25
example (seuil : Nat) (h : 0 < seuil) :
    ∃ s t : List Ecriture, conformeSous seuil s ∧ ¬ conformeSous seuil t := by
  obtain ⟨t, -, hnc⟩ := serie_bien_formee_agregat_non_conforme seuil h
  exact ⟨[⟨seuil⟩], t, PR19_ne_touche_pas_l_ecriture_isolee seuil ⟨seuil⟩ (Nat.le_refl _), hnc⟩
end PR19

section PR20
open ProfRegLot ProfRegPR20
-- n° 26
example (c : Creance) (a b : ProfRegLot.Actor) (hab : c a b = false) (hba : c b a = false) :
    lien c a b ≠ lien (fun x y => x == "A" && y == "B") "A" "B" := by
  rw [sans_creance_aucun_lien c a b hab hba, lien_temoin_discriminant.1]; decide
-- n° 27
example (c : Creance) (a b : ProfRegLot.Actor) (hab : c a b = false) (hba : c b a = false) :
    registreCommunalite c a b ≠ registreCommunalite (fun x y => x == "A" && y == "B") "A" "B" := by
  rw [absence_n_est_pas_lien_nul c a b hab hba, lien_temoin_discriminant.2]; decide
-- n° 28
example (c : Creance) (a : ProfRegLot.Actor) (h : c a a = false) :
    lien c a a ≠ lien (fun x y => x == "A" && y == "B") "A" "B" := by
  rw [sans_creance_sur_soi_pas_de_lien_a_soi c a h, lien_temoin_discriminant.1]; decide
-- n° 29 (invariance témoignée : même socle, registres financiers distincts)
example : ∃ (c : Creance) (a b : ProfRegLot.Actor),
    (registreAugmenteDe c).socle = (registreAugmenteBis c).socle
    ∧ (registreAugmenteDe c).pFin a b ≠ (registreAugmenteBis c).pFin a b := by
  obtain ⟨c, a, b, -, -, h⟩ := accord_sur_l_existence_pas_sur_la_valeur
  exact ⟨c, a, b, les_deux_registres_augmentes_ont_le_meme_socle c, h⟩
end PR20

section PR23
open ProfRegPR23
variable {A R K : Type}
-- n° 30 (témoin direct du 28/09)
example (a : A) (r : R) (k : K) (s : Situation) :
    ecartLisible (ecritureAvecMaintien a r k s : Ecriture A R K)
      ≠ ecartLisible (ecritureSansMaintien a s : Ecriture A R K) := by
  rw [(ecart_lisible_temoin_discriminant a r k s).1, (ecart_lisible_temoin_discriminant a r k s).2]; simp
-- n° 31
example (a : A) (r : R) (k : K) (s : Situation) (h : s.paye < s.du) :
    prioriteMord (ecritureSansMaintien a s : Ecriture A R K)
      ≠ prioriteMord (ecritureAvecMaintien a r k s : Ecriture A R K) := by
  rw [priorite_sans_assiette _ rfl, priorite_mord_si_inscrite a r k s h]; simp
end PR23

section PR25
open ProfRegLot ProfRegPR25
-- n° 32
example : ∃ (e : RegistreComptableAugmente Bool Bool) (a b : ProfRegLot.Actor),
    lectureCom temoinA.pCom temoinA.pleinCom "A" "B" ∧ ¬ lectureCom e.pCom e.pleinCom a b := by
  obtain ⟨h1, e, a, b, h2⟩ := la_lecture_com_temoin_discriminant
  exact ⟨e, a, b, h1, h2⟩
end PR25

section PR26
open ProfRegPR26
-- n° 33
example (hist : List Inscription) (i : Inscription) (h : i.etat = EtatExtinction.nonDeclare) :
    ∃ j k : Inscription, compteEteinte i ≠ compteEteinte j ∧ BienFormee hist i ≠ BienFormee [] k := by
  obtain ⟨j, -, -, hj⟩ := seul_debiteur_bien_forme_mais_marque
  obtain ⟨k, -, -, hk⟩ := deux_regimes_divergents_ne_suffisent_pas
  have := le_silence_ne_solde_rien hist i h
  exact ⟨j, k, by rw [this.2, hj]; decide, by rw [this.1, hk]; decide⟩
end PR26

section PR4
open ProfRegPR4
-- n° 34
example (e : Ecriture) (h : milieuDegradePersistant e = true) :
    ∃ e', phaseInventaireRequise e ≠ phaseInventaireRequise e' := by
  obtain ⟨e', h', -⟩ := PR4_temoin_discriminant.1
  exact ⟨e', by rw [milieu_degrade_persistant_declenche e h, h']; decide⟩
-- n° 35
example (e : Ecriture) (hd : phaseInventaireRequise e = true) (hi : e.inventaire = none) :
    ∃ e', cloturable e ≠ cloturable e' := by
  obtain ⟨e', -, h'⟩ := PR4_temoin_discriminant.2
  exact ⟨e', by rw [cloture_interdite_sans_inventaire e hd hi, h']; decide⟩
-- n° 36
example (e : Ecriture) (h : regimeDeclencheur e.regime = true) :
    ∃ e', phaseInventaireRequise e ≠ phaseInventaireRequise e' := by
  obtain ⟨e', h', -⟩ := PR4_temoin_discriminant.1
  exact ⟨e', by rw [(PR4_les_trois_declencheurs_suffisent_chacun e).1 h, h']; decide⟩
-- n° 37 (invariance en le contenu ; la fonction dépend de la présence de l'inventaire)
example : ∃ e₁ e₂ : Ecriture, cloturable e₁ ≠ cloturable e₂ := by
  obtain ⟨e₁, -, -, h₁⟩ := le_type_ne_produit_aucun_inventaire
  obtain ⟨e₂, -, h₂⟩ := PR4_temoin_discriminant.2
  exact ⟨e₁, e₂, by rw [h₁, h₂]; decide⟩
end PR4

section PR5
open ProfRegPR5
-- n° 38, 39 (invariance témoignée) : par le témoin nommé, puis sens par sens
example : (sensMR (sensRM ⟨false, true, true, true, false, false, false⟩)).precautionAsymetrique
    ≠ (⟨false, true, true, true, false, false, false⟩ : EtatMR).precautionAsymetrique := by
  rw [l_ordre_RM_puis_MR_inscrit_seul.1]; decide
example : (sensMR ⟨true, true, false, false, false, false, false⟩).precautionAsymetrique
    ≠ (⟨true, true, false, false, false, false, false⟩ : EtatMR).precautionAsymetrique := by decide
example : (sensRM ⟨false, true, true, true, false, false, false⟩).focalisationVictimaire
    ≠ (⟨false, true, true, true, false, false, false⟩ : EtatMR).focalisationVictimaire := by decide
-- n° 40
example : (lever ⟨true, true, true, true, true, true, true⟩).precautionAsymetrique
    ≠ (lever ⟨true, true, true, true, true, false, true⟩).precautionAsymetrique := by
  rw [le_carre_ferme_apres_l_acte _ rfl rfl, un_seul_des_deux_actes_ne_ferme_pas]; decide
end PR5

section PR7
open ProfRegPR7
-- n° 41, 43
example (s s' : Situation) (h6 : s.f6Actif = true) (ht : s.f6Traite = false) (ht' : s'.f6Traite = true) :
    traiter s Acte.certifierF10 ≠ traiter s' Acte.certifierF10 := by
  rw [F10_ne_certifie_pas_sous_F6_actif s h6 ht, F10_reprend_apres_traitement s' ht']; simp
-- n° 42
example (s : Situation) (h6 : s.f6Actif = true) (ht : s.f6Traite = false) :
    traiter s Acte.traiterF6 ≠ traiter s Acte.certifierF10 := by
  rw [traiter_F6_est_toujours_admis, F10_ne_certifie_pas_sous_F6_actif s h6 ht]; simp
-- n° 44 (invariance en le contenu ; l'admission dépend des drapeaux)
example (n : Nat) :
    (traiter ⟨true, false, false, false, n⟩ Acte.certifierF10).isSome
      ≠ (traiter ⟨true, false, true, false, n⟩ Acte.certifierF10).isSome := by
  rw [F10_ne_certifie_pas_sous_F6_actif _ rfl rfl, F10_reprend_apres_traitement _ rfl]; simp
-- n° 45
example (s s' : Situation) (h : s.f6Actif = false) (h6 : s'.f6Actif = true) (ht : s'.f6Traite = false) :
    traiter s Acte.certifierF10 ≠ traiter s' Acte.certifierF10 := by
  rw [PR7_ne_contraint_pas_hors_coactivation s h, F10_ne_certifie_pas_sous_F6_actif s' h6 ht]; simp
end PR7

section PR9
open ProfRegPR9
-- n° 46
example : ∃ c₁ c₂ : CanalEA, Termine c₁ ∧ ¬ Termine c₂ :=
  ⟨_, _, un_canal_qui_ne_relit_pas_le_seuil_termine (fun _ _ => 0), un_canal_qui_relit_le_seuil_ne_termine_pas⟩
end PR9

section V3V4
open ProfReg
-- n° 47, 48
example (i j : Interaction) (hi : i.regime = RegimeObligation.systemique)
    (hj : j.regime = RegimeObligation.actoriel) (hp : j.phase ≠ PhaseEnquete.deliberation) :
    chemin_direct i ≠ chemin_direct j := by
  rw [V3_aboutit_deliberation i hi, (V3_actoriel_inchange j hj).1]; exact Ne.symm hp
-- n° 49, 50
example (inv : InventaireNonVide) :
    ¬ transition_valide StatutDette.nonAttribuee NiveauRIA.critique
    ∧ transition_valide StatutDette.attribuee NiveauRIA.critique :=
  ⟨fun h => cascade_deliberation_before_critique _ _ rfl h rfl,
   (critique_released_by_porteur _ _ inv rfl rfl).2.1⟩
end V3V4

section VJE
open ProfReg VJE
-- n° 51, 55, 57
example (j j' : EtatJustice) (did : String) (hT : j.typeInj = TypeInjustice.hermeneutique)
    (hR : j.resistanceBloquante = true) (hR' : j'.resistanceBloquante = false) :
    (appliquerSensJE j did).metaluciditeRequise ≠ (appliquerSensJE j' did).metaluciditeRequise := by
  rw [(VJE_sensJE_declenche j did hT hR).1, VJE_sansResistance j' did hR']; decide
example (j j' : EtatJustice) (did : String) (hT : j.typeInj = TypeInjustice.hermeneutique)
    (hR : j.resistanceBloquante = true) (hR' : j'.resistanceBloquante = false) :
    (appliquerSensJE j did).metaluciditeRequise ≠ (appliquerSensJE j' did).metaluciditeRequise := by
  rw [(VJE_metalucidite_ssi j did).2 ⟨hT, hR⟩, VJE_sansResistance j' did hR']; decide
-- n° 52, 53, 54
example (e : EtatEvolutivite) (j j' : EtatJustice) (hRev : e.revisionEffectuee = true)
    (hP : j.persistance = PersistanceInjustice.episodique)
    (hP' : j'.persistance = PersistanceInjustice.structurelle) :
    (appliquerSensEJ e j).precondSatisfaite ≠ (appliquerSensEJ e j').precondSatisfaite := by
  rw [VJE_sensEJ_episodique e j hRev hP, VJE_sensEJ_structurel_bloque e j' hRev hP']; decide
example (e : EtatEvolutivite) (j j' : EtatJustice) (hRev : e.revisionEffectuee = true)
    (hP : j.persistance = PersistanceInjustice.episodique)
    (hP' : j'.persistance = PersistanceInjustice.structurelle) :
    (appliquerSensEJ e j).precondSatisfaite ≠ (appliquerSensEJ e j').precondSatisfaite := by
  rw [VJE_ferme_apres_revision_externe j e hRev, VJE_ferme_apres_revision_externe j' e hRev, hP, hP']
  decide
-- n° 56
example (j j' : EtatJustice) (did : String) (hT : j.typeInj = TypeInjustice.hermeneutique)
    (hR : j.resistanceBloquante = true) (hR' : j'.resistanceBloquante = false) :
    (appliquerSensJE j' did).sourceResistanceDID ≠ (appliquerSensJE j did).sourceResistanceDID := by
  rw [VJE_sansResistance_sourceDID j' did hR', (VJE_sensJE_declenche j did hT hR).2]; simp
end VJE

section Interactions
-- n° 58
example (d d' : SystemicInteraction) (h : d.creditor = none) (h' : d'.creditor.isSome = true) :
    ¬ R1_systemique d ∧ R1_systemique d' :=
  ⟨systemique_sans_creancier_viole_R1 d h, (R1_systemique_ssi_creancier d').2 h'⟩
end Interactions

section Relecture45
-- Lectures reclassées à la relecture des 45 universels à preuve longue (n° 59 à 68)
-- n° 59
example (collectif : Finset Actor) (amount : ENNReal) (d' : SystemicInteraction)
    (h' : d'.creditor.isSome = true) :
    ¬ R1_systemique { collectif := collectif, creditor := none, amount := amount } ∧ R1_systemique d' :=
  ⟨systemique_requires_R1_extension collectif amount, (R1_systemique_ssi_creancier d').2 h'⟩
-- n° 60 (invariance témoignée : le statut est conservé, le porteur change)
example {A : Type} (a b : A) (st : ProfRegPR11.StatutObl) (hab : a ≠ b) :
    ∃ (r : ProfRegPR11.RegimeDevolution A) (o' : ProfRegPR11.Obligation A),
      ProfRegPR11.appliquer r ⟨a, st⟩ ProfRegPR11.Evenement.disparitionDuPorteur = some o'
      ∧ o'.statut = st ∧ o'.porteur ≠ a := by
  obtain ⟨r, hr⟩ := ProfRegPR11.devolution_libre_reconstitue_la_cession a b st
  exact ⟨r, ⟨b, st⟩, hr, ProfRegPR11.la_devolution_ne_solde_pas r ⟨a, st⟩ ⟨b, st⟩ hr, Ne.symm hab⟩
-- n° 61
example {A : Type} (hne : ProfRegPR16.NonEnumerable A) (c c' : ProfRegPR16.ConditionRefutation A)
    (h : c.refutantsAdmis = none) (l : List A) (h' : c'.refutantsAdmis = some l) :
    ∃ a, ProfRegPR16.ExercablePar c a ∧ ¬ ProfRegPR16.ExercablePar c' a := by
  obtain ⟨a, ha⟩ := ProfRegPR16.liste_close_exclut_toujours hne c' l h'
  exact ⟨a, ProfRegPR16.ouverture_n_exclut_personne c h a, ha⟩
-- n° 62
example {A R K : Type} (a : A) (r : R) (k : K) (s : ProfRegPR23.Situation) (h : s.paye < s.du) :
    ∃ ec : ProfRegPR23.Ecriture A R K,
      ProfRegPR23.prioriteMord (ProfRegPR23.ecritureAvecMaintien a r k s : ProfRegPR23.Ecriture A R K)
        ≠ ProfRegPR23.prioriteMord ec := by
  obtain ⟨ec, -, hec⟩ := ProfRegPR23.PR23_n_affirme_aucune_dette a r k
  exact ⟨ec, by rw [ProfRegPR23.priorite_mord_si_inscrite a r k s h, hec]; decide⟩
-- n° 63, 64
example (e e' : ProfRegPR5.EtatMR) (hf : e.focalisationVictimaire = true)
    (hm : e.meconnaissanceFondatrice = true) (hm' : e'.meconnaissanceFondatrice = false)
    (hp : e'.precautionAsymetrique = false) :
    (ProfRegPR5.sensMR e).precautionAsymetrique ≠ (ProfRegPR5.sensMR e').precautionAsymetrique := by
  rw [ProfRegPR5.PR5_ne_refute_pas_le_couplage e hf hm,
      ProfRegPR5.PR5_ne_juge_pas_la_meconnaissance e' hm', hp]; decide
-- n° 65 (invariance témoignée : le contenu est conservé, f6Traite change)
example (s : ProfRegPR7.Situation) (h : s.f6Traite = false) :
    ∃ s', ProfRegPR7.traiter s ProfRegPR7.Acte.traiterF6 = some s'
      ∧ s'.contenu = s.contenu ∧ s'.f6Traite ≠ s.f6Traite :=
  ⟨_, ProfRegPR7.traiter_F6_est_toujours_admis s,
   ProfRegPR7.PR7_ne_touche_pas_au_contenu s _ _ (ProfRegPR7.traiter_F6_est_toujours_admis s),
   by simp [h]⟩
-- n° 66
example (inv : ProfReg.InventaireNonVide) :
    ¬ ProfReg.transition_valide ProfReg.StatutDette.nonAttribuee ProfReg.NiveauRIA.critique
    ∧ ProfReg.transition_valide ProfReg.StatutDette.attribuee ProfReg.NiveauRIA.critique :=
  ⟨(ProfReg.V4_cascade_coherente _ rfl).1, (ProfReg.critique_released_by_porteur _ _ inv rfl rfl).2.1⟩
-- n° 67
example (j j' : VJE.EtatJustice) (did : String) (hT : j.typeInj = VJE.TypeInjustice.hermeneutique)
    (hR : j.resistanceBloquante = true) (hT' : j'.typeInj ≠ VJE.TypeInjustice.hermeneutique) :
    (VJE.appliquerSensJE j did).metaluciditeRequise ≠ (VJE.appliquerSensJE j' did).metaluciditeRequise := by
  rw [(VJE.VJE_sensJE_declenche j did hT hR).1, VJE.VJE_pasDeJE_horsHermeneutique j' did hT']; decide
-- n° 68
example (e : ProfRegPR9.EtatEA) (h : e.modificateurAffectif = true) :
    (ProfRegPR9.canalAE e).resistanceForte ≠ (ProfRegPR9.canalAE ⟨false, false, 0⟩).resistanceForte := by
  rw [ProfRegPR9.PR9_ne_supprime_pas_le_canal_AE e h, ProfRegPR9.PR9_canalAE_temoin_discriminant]; decide
end Relecture45

section D15
open ProfReg V10 ProfRegPR8
-- n° 69 (D-15) : la caractérisation rend les deux valeurs
example (c c' : ContexteProspectif) (h : c.legitimite = LegitimiteRepresentant.pratique)
    (h' : c'.legitimite = LegitimiteRepresentant.juridique) :
    RefutationObligatoire c ∧ ¬ RefutationObligatoire c' :=
  ⟨(exactement_deux_regimes_obliges c).2 (by rw [h]; decide),
   fun hr => (exactement_deux_regimes_obliges c').1 hr (Or.inr h')⟩
end D15

section Conventions
open ProfReg V10 ProfRegPR28
-- n° 70 (conventions, 28/09) : la garde de CONV-6 et son témoin rendent les deux valeurs
example : ∃ e₁ e₂ : EcritureEngagee, SatisfaitCONV6 e₁ ∧ ¬ SatisfaitCONV6 e₂ := by
  obtain ⟨e₂, -, -, h₂⟩ := BienFormee_ne_borne_pas_la_prospective
  exact ⟨⟨⟨StatutDette.attribuee, HorizonTemporel.institutionnel, none,
      LegitimiteRepresentant.deliberative, none⟩, none⟩, e₂,
    CONV6_ne_vaut_pas_dans_l_exercice _ rfl, h₂⟩
end Conventions

section GroupeC
open ProfRegPR29 ProfRegPR30 ProfRegPR31
-- Groupe C (audit §3.2), 28/09 : pour chaque lecture, le témoin nommé rend une autre valeur.
-- n° 71 PR-29 trois_livres_sans_tiers_mal_formee / trois_livres_temoin_discriminant
example : bienFormeeArite ⟨.troisLivres, some 1, none, some 0⟩
    ≠ bienFormeeArite ⟨.troisLivres, some 1, some 2, some 0⟩ := by decide
-- n° 72 PR-30 non_determinable_rend_indetermine / la_branche_B_exclut_le_capital_d_apporteur
example : qualifiant ⟨false, .nonDeterminable⟩ ≠ qualifiant ⟨false, .vrai⟩ := by decide
-- n° 73 PR-30 le_non_declare_ne_qualifie_pas_et_marque / qualifiant_temoin_discriminant
example : qualifiant ⟨false, .nonDeclare⟩ ≠ qualifiant ⟨true, .nonDeclare⟩
    ∧ marqueurSansQualification ⟨false, .nonDeclare⟩ ≠ marqueurSansQualification ⟨true, .nonDeclare⟩ := by decide
-- n° 74 PR-30 une_classe_non_repartissable_suffit / la_qualification_agregee_n_est_pas_la_qualification_par_classe
example : qualifieParClasse [(.usage, .faux)] ≠ qualifieParClasse [(.valeurEconomique, .vrai)] := by decide
-- n° 75 PR-30 classe_manquante_rend_indetermine / la_completude_prime_sur_la_classe_qualifiante
example : statutFiducie [(.usage, .faux)] ≠ statutFiducie [(.usage, .faux), (.valeurEconomique, .vrai)] := by decide
-- n° 76 PR-30 citer_ses_regles_n_engage_pas_les_tiers / droit_d_ecrire_n_est_pas_pouvoir_d_engager
example : engage ⟨some .reglesPropresCollectif⟩ false ≠ engage ⟨some .reglesPropresCollectif⟩ true := by decide
-- n° 77 PR-30 la_pratique_seule_marque_et_ne_qualifie_pas / droit_d_ecrire_n_est_pas_pouvoir_d_engager
example : estDPlusDeCommun ⟨none⟩ ≠ estDPlusDeCommun ⟨some .reglesPropresCollectif⟩ := by decide
-- n° 78 PR-31 sans_ancrage_refusee / le_registre_de_communalite_suffit
example : ancree ⟨none, none⟩ ≠ ancree ⟨none, some 1⟩ := by decide
-- n° 79 PR-31 sans_objet_sans_motif_est_un_nondeclare_renomme / G4_n_admet_pas_le_titulaire_non_humain
example : effet .G1 (.sansObjetMotive none) ≠ effet .G1 (.sansObjetMotive (some .titulaireNonHumain)) := by decide
-- n° 80 PR-31 le_motif_refute_requalifie (l'énoncé porte les deux valeurs)
example : requalifier (.sansObjetMotive (some (.autre 0))) true
    ≠ requalifier (.sansObjetMotive (some (.autre 0))) false := by decide
-- n° 81 PR-31 representant_sans_dimension_mal_forme / P7_temoin_discriminant
example : bienFormeeP7 ⟨some true, [1], []⟩ ≠ bienFormeeP7 ⟨some true, [1], [.avec]⟩ := by decide
end GroupeC

section C9
open ProfRegPR32
-- n° 82 PR-32 regime_sans_refutation_n_autorise_aucune_ecriture / regime_temoin_discriminant
example : autoriseEcriture ⟨some 1, some 2, none, some 4, some 5⟩
    ≠ autoriseEcriture ⟨some 1, some 2, some 3, none, none⟩ := by decide
end C9

section Critere
open ProfRegPR33 ProfRegPR34
-- n° 83 PR-33 sans_branche_pas_de_classement / classement_de_reference
example : classer aucun ≠ classer conv8 := by decide
-- n° 84 PR-34 hote_non_declare_delibere / P5_temoin_discriminant
example : effetP5 ⟨.instrumentation, .nonRenseigne, false⟩
    ≠ effetP5 ⟨.instrumentation, .declare ⟨some 1, some 2, some .imposee⟩, false⟩ := by decide
-- n° 85 PR-34 la_voie_intermediaire_ne_dispense_pas_du_triplet / P5_temoin_discriminant
example : (effetP5 ⟨.instrumentation, .declare ⟨some 1, none, some .aucuneImposee⟩, false⟩).isSome
    ≠ (effetP5 ⟨.instrumentation, .declare ⟨some 1, some 2, some .imposee⟩, false⟩).isSome := by decide
end Critere

/-! ## Ajout du 2 octobre 2026 — lignes n° 86 à 122 (PR-37 à PR-50)
Mêmes règles que ci-dessus : chaque `example` montre, à partir de la lecture
et de son témoin nommés, que la fonction lue rend une autre valeur sur
l'entrée du témoin (ou, pour une invariance témoignée, que la fonction
modifie un autre champ). -/

section PR50
open ProfRegPR50
-- n° 86 PR-50 seuil_non_declare_ne_signale_pas / signal_temoin_discriminant
example : signal carreTemoin ecartNat none () ≠ signal carreTemoin ecartNat (some 1) () := by decide
end PR50

section PR37
open ProfRegPR35 (Entite Registre Ligne)
open ProfRegPR37
-- n° 87 PR-37 sans_registre_l_ecart_reste_inscrit / registre_de_milieu_temoin_discriminant
example : ecartEnversMilieu 2026 registreEntreprise riviere none
    ≠ ecartEnversMilieu 2026 registreEntreprise riviere (some (regR .arretee)) := by decide
-- n° 88 PR-37 la_ratification_ne_fonde_pas_le_registre / ecriture_duale_avec_un_milieu
example (r : RegistreDuMilieu Nat) (h : r.declaration.mode = .ratifiee) :
    (registreOpposable 2026 (some r)).isSome ≠ (registreOpposable 2026 (some (regR .arretee))).isSome := by
  rw [la_ratification_ne_fonde_pas_le_registre 2026 r h]; decide
-- n° 89 PR-37 sans_declaration_pas_de_registre / ecriture_duale_avec_un_milieu
example (r : RegistreDuMilieu Nat) (h : r.declaration.mode = .nonDeclare) :
    (registreOpposable 2026 (some r)).isSome ≠ (registreOpposable 2026 (some (regR .arretee))).isSome := by
  rw [sans_declaration_pas_de_registre 2026 r h]; decide
-- n° 90 PR-37 sans_critere_d_inclusion_pas_de_registre / ecriture_duale_avec_un_milieu
example (r : RegistreDuMilieu Nat) (h : r.declaration.inclusion = none) :
    (registreOpposable 2026 (some r)).isSome ≠ (registreOpposable 2026 (some (regR .arretee))).isSome := by
  rw [sans_critere_d_inclusion_pas_de_registre 2026 r h]; decide
-- n° 91 PR-37 sans_interprete_pas_de_registre / ecriture_duale_avec_un_milieu
example (r : RegistreDuMilieu Nat) (h : r.declaration.interprete = none) :
    (registreOpposable 2026 (some r)).isSome ≠ (registreOpposable 2026 (some (regR .arretee))).isSome := by
  rw [sans_interprete_pas_de_registre 2026 r h]; decide
-- n° 92 PR-37 sans_interprete_le_marqueur_PR31_se_leve / le_marqueur_de_milieu_se_leve_exactement_sur_l_interprete_manquant
example (d : DeclarationConcernes) (s p : Nat) (h : d.interprete = none) :
    ProfRegPR31.marqueurSansInterprete (versInscriptionMilieu d (some s) (some p))
      ≠ ProfRegPR31.marqueurSansInterprete ⟨0, some 1, some 2, some 3⟩ := by
  rw [sans_interprete_le_marqueur_PR31_se_leve d s p h]; decide
-- n° 93 PR-37 sans_maintien_pas_d_appui / ecriture_duale_avec_un_milieu
example (r : RegistreDuMilieu Nat) (h : r.maintien = none) :
    (registreOpposable 2026 (some r)).isSome ≠ (registreOpposable 2026 (some (regR .arretee))).isSome := by
  rw [sans_maintien_pas_d_appui 2026 r h]; decide
-- n° 94 PR-37 maintien_d_un_autre_registre_pas_d_appui / ecriture_duale_avec_un_milieu
example (r : RegistreDuMilieu Nat) (m : MaintienMilieu) (hm : r.maintien = some m)
    (h : m.registre ≠ r.declaration.titulaire) :
    (registreOpposable 2026 (some r)).isSome ≠ (registreOpposable 2026 (some (regR .arretee))).isSome := by
  rw [maintien_d_un_autre_registre_pas_d_appui 2026 r m hm h]; decide
end PR37

section PR39
open ProfRegPR39
-- n° 95 PR-39 sans_constat_rien_n_est_decharge / attendu_n_est_pas_constate
example : resteOuvert effortSeul riviere ≠ resteOuvert constatRiverain riviere := by decide
-- n° 96 PR-39 le_constat_ramene_a_la_dette_de_preservation / attendu_n_est_pas_constate
example : resteOuvert constatRiverain riviere ≠ resteOuvert effortSeul riviere := by decide
end PR39

section PR40
open ProfRegPR35 (Ligne)
open ProfRegPR40
-- n° 97 PR-40 la_communication_ne_change_pas_l_ecart / statut_temoin_discriminant (invariance témoignée)
example : statut .extraitCommunique regA regBVide ⟨fournisseur, .Dplus, 10⟩
    ≠ statut .nonCommunique regA regBVide ⟨fournisseur, .Dplus, 10⟩ := by decide
-- n° 98 PR-40 en_ecriture_duale_rien_a_qualifier / non_verifiable_n_est_pas_constate
example : ecartQualifie .nonCommunique regA regBVide ≠ [] := by decide
end PR40

section PR41
open ProfRegPR41
-- n° 99 PR-41 aucun_teneur_ne_tranche / arbitrer_temoin_discriminant
example : arbitrer .conteste (some ⟨entreprise, false, .confirme⟩) entreprise fournisseur
    ≠ arbitrer .conteste (some ⟨communauteDeControle, false, .confirme⟩) entreprise fournisseur := by decide
-- n° 100 PR-41 un_tiers_lie_ne_tranche_pas / arbitrer_temoin_discriminant
example : arbitrer .conteste (some ⟨communauteDeControle, true, .confirme⟩) entreprise fournisseur
    ≠ arbitrer .conteste (some ⟨communauteDeControle, false, .confirme⟩) entreprise fournisseur := by decide
-- n° 101 PR-41 l_arbitrage_n_efface_rien / le_tiers_tranche_la_contestation (invariance témoignée)
example : ecartArbitre .extraitCommunique ProfRegPR40.regA ProfRegPR40.regBNie
      (fun _ => some ⟨communauteDeControle, false, .confirme⟩)
    ≠ ecartArbitre .extraitCommunique ProfRegPR40.regA ProfRegPR40.regBNie
      (fun _ => some ⟨communauteDeControle, false, .infirme⟩) := by decide
end PR41

section PR43
open ProfRegPR43
-- n° 102 PR-43 sans_instance_commune_rien_n_est_arbitre / seule_l_instance_commune_tranche
example : arbitrerInstitue dsCommun .conteste (some ⟨bureauEtudes, false, .confirme⟩) entreprise riviere
    ≠ arbitrerInstitue dsCommun .conteste (some ⟨comiteDuFleuve, false, .confirme⟩) entreprise riviere := by decide
-- n° 103 PR-43 l_instance_liee_n_arbitre_pas / seule_l_instance_commune_tranche
example : arbitrerInstitue dsCommun .conteste (some ⟨comiteDuFleuve, true, .confirme⟩) entreprise riviere
    ≠ arbitrerInstitue dsCommun .conteste (some ⟨comiteDuFleuve, false, .confirme⟩) entreprise riviere := by decide
end PR43

section PR44
open ProfRegPR44
-- n° 104 PR-44 le_parcours_n_efface_rien / statut_constat_temoin_discriminant (invariance témoignée)
example : (suivre dsRiviere riviere entrepriseX ligneX none none).statut
    ≠ (suivre dsRiviere riviere entrepriseX ligneX (some attMesures) none).statut := by decide
-- n° 105 PR-44 sans_attestation_rien_n_est_porte / statut_constat_temoin_discriminant
example : statutConstat dsRiviere riviere entrepriseX none none
    ≠ statutConstat dsRiviere riviere entrepriseX (some attMesures) none := by decide
-- n° 106 PR-44 sans_consentement_la_voie_privee_est_fermee / l_arbitrage_exige_une_convention
example : saisineRecevable ⟨.arbitrage, .quelconque, false, none⟩
    ≠ saisineRecevable ⟨.arbitrage, .quelconque, true, none⟩ := by decide
-- n° 107 PR-44 la_voie_publique_ignore_le_refus / l_arbitrage_exige_une_convention (invariance témoignée)
example : saisineRecevable ⟨.arbitrage, .quelconque, false, none⟩
    ≠ saisineRecevable ⟨.arbitrage, .quelconque, true, none⟩ := by decide
-- n° 108 PR-44 l_autorite_de_supervision_ne_depend_pas_de_la_societe / sans_consentement_la_voie_privee_est_fermee
example : saisineRecevable ⟨.autoriteSupervision, .quelconque, false, none⟩
    ≠ saisineRecevable ⟨.negociation, .quelconque, false, none⟩ := by decide
end PR44

section PR45
open ProfRegPR44 (dsRiviere riviere entrepriseX ligneX)
open ProfRegPR45
-- n° 109 PR-45 conv17_sans_protocole_hors_protocole / chaque_rubrique_compte
example : statut17 dsRiviere riviere protoSansDemande .registre (some ⟨.autoriteAdministrative, .quelconque, false, none⟩)
    ≠ statut17 dsRiviere riviere protoConforme .registre (some ⟨.autoriteAdministrative, .quelconque, false, none⟩) := by decide
-- n° 110 PR-45 conv17_n_interdit_pas_de_signaler / chaque_rubrique_compte
example : statut17 dsRiviere riviere protoConforme (.membre hydrologue) (some ⟨.autoriteAdministrative, .quelconque, false, none⟩)
    ≠ statut17 dsRiviere riviere protoConforme .registre (some ⟨.autoriteAdministrative, .quelconque, false, none⟩) := by decide
-- n° 111 PR-45 conv17_avec_protocole_retrouve_PR44 / conforme_temoin_discriminant
example : statut17 dsRiviere riviere protoConforme .registre (some ⟨.autoriteAdministrative, .quelconque, false, none⟩)
    ≠ statut17 dsRiviere riviere protoSansDemande .registre (some ⟨.autoriteAdministrative, .quelconque, false, none⟩) := by decide
-- n° 112 PR-45 la_reconstitution_suppose_un_detenteur_tiers / confronter_temoin_discriminant
example : confronter ligneX (some ⟨entrepriseX, entrepriseX, 120⟩)
    ≠ confronter ligneX (some ⟨entrepriseX, prefet, 120⟩) := by decide
end PR45

section PR46
open ProfRegPR44 (saisineRecevable)
open ProfRegPR46
-- n° 113 PR-46 directement_lie_pas_de_dette_de_reparation / qualifier_temoin_discriminant
example : qualifier .directementLie .reparation ≠ qualifier .cause .reparation := by decide
-- n° 114 PR-46 exiger_n_endette_pas / qualifier_temoin_discriminant
example : qualifier .cause .correctionExigee ≠ qualifier .cause .reparation := by decide
-- n° 115 PR-46 la_signature_vaut_consentement_ex_ante / la_signature_n_ouvre_pas_la_transaction
example : saisineRecevable ⟨.arbitrage, .quelconque, consentPour .arbitrage true false, none⟩
    ≠ saisineRecevable ⟨.transaction, .quelconque, consentPour .transaction true false, none⟩ := by decide
end PR46

section PR47
open ProfRegPR46 (comitePilotage dsChaine objetsAccord)
open ProfRegPR47
-- n° 116 PR-47 sans_site_destination_non_declaree / etat18_temoin_discriminant
example : etat18 dsChaine comitePilotage objetsAccord { eDeclare with annotation := { annotComplete with site := none } }
    ≠ etat18 dsChaine comitePilotage objetsAccord eRequalifie := by decide
-- n° 117 PR-47 le_lien_retenu_prime / etat18_temoin_discriminant
example : etat18 dsChaine comitePilotage objetsAccord eRequalifie
    ≠ etat18 dsChaine comitePilotage objetsAccord eDeclare := by decide
end PR47

section PR48
open ProfRegPR35 (ecart)
open ProfRegPR46 (marque1 comitePilotage dsChaine)
open ProfRegPR48
-- n° 118 PR-48 non_fondee_est_une_contestation / issue_plainte_temoin_discriminant
example : issuePlainte dsChaine marque1 comitePilotage .nonFondee none none
    ≠ issuePlainte dsChaine marque1 comitePilotage .fondee none none := by decide
-- n° 119 PR-48 plainte_non_retenue_rien_ne_change / le_miroir_force_sur_l_instance
example : ecart plainteR (miroirApres (.trancheeParInstance false) regMarque plainteR)
    ≠ ecart plainteR (miroirApres (.trancheeParInstance true) regMarque plainteR) := by decide
end PR48

section PR49
open ProfRegPR39 (etat effortSeul constatRiverain)
open ProfRegPR49
-- n° 120 PR-49 la_conformite_ne_vaut_pas_realisation / conformite_et_realisation_independantes
example : etat effortSeul ProfRegPR39.riviere ≠ etat constatRiverain ProfRegPR39.riviere := by decide
-- n° 121 PR-49 sans_mise_en_demeure_irrecevable / injonction_temoin_discriminant
example : injonctionRecevable .stricte saisineAsso ⟨false, 3, true⟩
    ≠ injonctionRecevable .stricte saisineAsso ⟨true, 3, true⟩ := by decide
-- n° 122 PR-49 avant_trois_mois_irrecevable / injonction_temoin_discriminant
example : injonctionRecevable .stricte saisineAsso ⟨true, 2, true⟩
    ≠ injonctionRecevable .stricte saisineAsso ⟨true, 3, true⟩ := by decide
end PR49

section PR31_D7
-- D7 (b), 07/10/2026 : ancrage d'une écriture duale élargi à deux teneurs quelconques.
-- n° 123 PR-31 ancree_duale_ssi / deux_comptabilites_tenues_ancrent_une_duale ; la_duale_exige_un_ancrage_par_cote
example : ProfRegPR31.ancreeDuale ⟨0, ⟨some 1, none⟩⟩ ⟨1, ⟨some 2, none⟩⟩
    ≠ ProfRegPR31.ancreeDuale ⟨0, ⟨some 1, none⟩⟩ ⟨1, ⟨none, none⟩⟩ := by decide
example : ProfRegPR31.ancreeDuale ⟨0, ⟨some 1, none⟩⟩ ⟨1, ⟨some 2, none⟩⟩
    ≠ ProfRegPR31.ancreeDuale ⟨0, ⟨some 1, none⟩⟩ ⟨0, ⟨some 2, none⟩⟩ := by decide
end PR31_D7

/-! ## Ajout du 11 octobre 2026 — lignes n° 124 et 125 (PR-51) -/
section PR51
open ProfRegPR51
-- n° 124 PR-51 le_chemin_direct_n_est_pas_admissible / carre_temoin_discriminant
example : admissible eSystemiqueInventoriee cheminDirect ≠ admissible eActorielSansDeclencheur cheminDirect := by decide
-- n° 125 PR-51 entrer_en_deliberation_exige_l_inventaire / carre_temoin_discriminant
example : pas eSystemiqueInventoriee .inscription .deliberation ≠ pas eActorielSansDeclencheur .inscription .deliberation := by decide
end PR51
