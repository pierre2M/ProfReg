/-
  Audit.lean — audit d'axiomes du set ProfReg
  ===========================================

  Généré mécaniquement le 7 septembre 2026 (régénéré après la refondation VJE) à partir
  d'import de `ProfReg.lean` et des déclarations `theorem` /
  `lemma` réellement présentes dans les sources.

  POURQUOI MÉCANIQUEMENT : une liste écrite à la main peut oublier
  un théorème — et c'est précisément le théorème oublié qui
  pourrait importer un `sorryAx` sans qu'on le voie.

  POURQUOI DES NOMS QUALIFIÉS : les théorèmes vivent dans huit
  espaces de noms distincts (ProfReg, V4c, V10, V10b, VJE,
  ProfRegLot, ProfRegD4, ProfRegPR10, ProfRegPR3, ProfRegPR8).
  Sans qualification, la plupart des noms ne se résolvent pas.

  CE QU'IL FAUT LIRE DANS LA SORTIE :
    · « does not depend on any axioms »  -> le mieux
    · « depends on axioms: [propext] »   -> normal, sans danger
    · « ... [Classical.choice, Quot.sound, propext] » -> normal
    · « sorryAx » N'IMPORTE OÙ          -> THÉORÈME NON PROUVÉ,
       même si aucun `sorry` n'apparaît dans son fichier :
       il en importe un. C'EST LE SEUL CONTRÔLE RIGOUREUX.

  Lancer :  lake env lean Audit.lean 2>&1 | tee ../audit_2026-09-07.log
  Puis   :  grep -c sorryAx ../audit_2026-09-07.log

  Total des déclarations auditées : 604  (architecture 584 · texte 20)
  [PR-59 — 13/10/2026 : 596 → 604. Écart formel / réel droit par droit (cinq seuils, deux cycles,
   non instruit ≠ nul, sans faisceau) ; inclusivité instance par instance, second sens de la
   séparabilité sur l'instance de contrôle ; importe PR-58 ; huit théorèmes : 4 propext, 4 sans
   axiome ; aucun Classical.choice ; vérifiés hors Mathlib le 13/10.]
  [PR-58 — 13/10/2026 : 587 → 596. Un commun suppose ses instances (NT-ARCH §8.5.6.4) ; les axes de
   communalité se déclarent séparément (NT-G6 §2.1) ; neuf théorèmes : 8 propext, 1 sans axiome ;
   aucun Classical.choice ; vérifiés hors Mathlib le 13/10.]
  [PR-57 — 12/10/2026 : 577 → 587. Phase RECHERCHE_INTERVENTION : constat d'effet, recevabilité,
   CONTRE_PERFORMATIVITE_ATTESTEE, relance, déclencheurs ; importe PR-54 ; dix théorèmes : 7 propext,
   2 propext + Quot.sound, 1 sans axiome ; aucun Classical.choice ; vérifiés hors Mathlib le 12/10.]
  [PR-56 — 12/10/2026 : 570 → 577. Consentement par personne (champ global dérivé) et absence opposable
   (trace ou attestation de l'instance, contestation) ; importe PR-55 ; sept théorèmes : 3 propext,
   2 propext + Quot.sound, 2 sans axiome ; aucun Classical.choice ; vérifiés hors Mathlib le 12/10.]
  [12/10/2026 : `ProfRegPR13.le_mensonge_irait_dans_les_deux_sens` renommé
   `le_mensonge_sur_les_niveaux_irait_dans_les_deux_sens` (nom court déjà porté par PR-12) ; décompte inchangé.]
  [PR-54, PR-55 — 12/10/2026 : 555 → 570. PR-54 (NT-G4 : boucle confirmante et contre-performativité,
   importe PR-34) : huit théorèmes, 7 propext, 1 sans axiome. PR-55 (CORPUS_NON_CONSENTI : signal, blocage,
   sortie ; décisions du porteur n° 42 et 43) : sept théorèmes, 2 propext, 1 propext + Quot.sound,
   4 sans axiome ; aucun Classical.choice ; vérifiés hors Mathlib le 12/10 (Lean v4.31.0-rc1).]
  [PR-53 — 12/10/2026 : 544 → 555. Canal G-JUSTICE → G-AFFECTIF : onze théorèmes, sans Mathlib
   (importe PR-52 et PR-33), 5 propext, 6 sans axiome ; vérifiés hors Mathlib le 12/10.]
  [12/10/2026 : 543 → 544. PR-33, branche 1bis du critère (décision du porteur) :
   `l_inscription_dommageable_est_refusee_avant_tout_marqueur`, sans axiome ; vérifié hors Mathlib.]
  [PR-52 — 12/10/2026 : 536 → 543. Qualification du régime affectif (NT-G9 ; CONV-19, CONV-20) : sept théorèmes,
   sans Mathlib, 3 propext, 4 sans axiome, aucun Classical.choice ; vérifiés hors Mathlib le 12/10 (Lean v4.31.0-rc1).]
  [11-12/10/2026 : 539 → 536. Audit des 115 théorèmes que le set ne nomme pas : retrait de trois doublons
   d'énoncé — `ProfRegPR24.les_relations_indexees_par_Nat_ne_sont_pas_enumerables` et
   `ProfRegPR22.les_collectifs_indexes_par_Nat_ne_sont_pas_enumerables` (= `ProfRegPR16.nat_non_enumerable` ;
   l'unique usage du second, `une_liste_close_de_collectifs_Nat_exclut_quelqu_un`, pointe sur `nat_non_enumerable`),
   et `ProfRegPR19.aucun_seuil_positif_n_echappe` (= `ProfRegPR19.serie_bien_formee_agregat_non_conforme`).]
  [PR-51 — 11/10/2026 : 533 → 539. Carré B1↔B2, appui de CONV-2 étendue : six théorèmes, sans Mathlib,
   6 propext, aucun Classical.choice ; vérifiés hors Mathlib le 11/10 (PR-4 et PR-51, Lean v4.31.0-rc1).]
  [D7 (b) — 07/10/2026 : 529 → 533. PR-31 : ancrage d'une écriture duale élargi à deux teneurs quelconques
   (`CoteDuale`, `ancreeDuale`) ; `la_duale_exige_un_ancrage_par_cote` restaté sur `ancreeDuale` ; quatre théorèmes
   ajoutés (`ancree_duale_ssi`, `deux_comptabilites_tenues_ancrent_une_duale`, `le_registre_de_communalite_ancre_un_cote`,
   `un_seul_teneur_pas_de_duale`), 1 sans axiome chacun ; vérifiés hors Mathlib le 07/10 (PR-31 et ses dépendants).]
  [PR-50 — 02/10/2026 : 522 → 529. Forme du signal carre_non_commutatif (F3) : sept théorèmes, sans Mathlib,
   6 propext, 1 sans axiome, aucun Classical.choice. Build du porteur 529 / 0 / 10 confirmé (1 981 jobs ;
   ../audit_2026-10-02_PR50.log).]
  [D-ED-37 — 30/09/2026 : 519 → 522. Trois formes générales : PR-38 `la_consolidation_efface_toujours_la_paire`, PR-43 `l_instance_commune_tranche_toujours`, PR-46 `l_etoile_est_toujours_duale`. Build du porteur 519 / 0 / 10 confirmé (1 980 jobs).]
  [D-ED-34, 35 — 30/09/2026 : 512 → 519. PR-49 (7). PR-44 : voie `injonctionVigilance`, qualité `interetAAgir` (sans théorème ajouté). Build du porteur 512 / 0 / 10 confirmé.]
  [D-ED-30 — 30/09/2026 : 504 → 512. PR-44 +1 (voie autorité de supervision) ; PR-48 (7, qualification des plaintes). Build du porteur 504 / 0 / 10 confirmé.]
  [D-ED-26 à 29 — 30/09/2026 : 496 → 504. PR-44 +1 (voie arbitrage, D-ED-29) ; PR-46 +1 (la signature n'ouvre pas la transaction) ; PR-47 (6, CONV-18).]
  [D-ED-18 — 30/09/2026 : 485 → 496. PR-46 (11, registre de chaîne : étoile, qualification par le lien OCDE, miroir forcé par plainte fondée, consentement ex ante). Build du porteur 485 / 0 / 10 confirmé.]
  [D-ED-22, 23, 24 — 30/09/2026 : 476 → 485. PR-45 (9, protocole d'attestation, CONV-17, miroir reconstitué).]
  [D-ED-21 — 30/09/2026 : 464 → 476. PR-44 (12, constat unilatéral : attestation interne, tiers extérieur). Build du porteur 464 / 0 / 10 confirmé.]
  [D-ED-20 — 30/09/2026 : 457 → 464. PR-43 (7, instance de contrôle commune : tiers institué, CONV-16).]
  [D-ED-12 et D-ED-17 — 30/09/2026 : 444 → 457. PR-41 (6, arbitrage de l'écart par un tiers, ISA 505) ;
   PR-42 (7, teneurs indépendants : l'écriture duale fait preuve seule entre indépendants, avec tiers sinon).]
  [D-ED-13, 14, 15 — 30/09/2026 : 425 → 444. PR-37 révisé 10 → 16 (déclaration des concernés : critère
   d'inclusion, interprète, réexamen, nature du titulaire) ; PR-39 (7, réalisation du maintien) ;
   PR-40 (6, statut de l'écart).]
  [D-ED-16, 30/09/2026 : 419 → 425. PR-23 +4 (structure MaintienCONV11 à six éléments, solde calculé) ;
   PR-37 révisé 8 → 10 : `maintien_non_structure_pas_d_appui` → `sans_maintien_pas_d_appui`,
   `sans_horizon_l_ecart_revient` → `registre_mal_nomme_l_ecart_revient`, + `maintien_d_un_autre_registre_pas_d_appui`,
   + `la_dette_de_preservation_du_milieu_est_calculee`.]
  [D-ED-10, 30/09/2026 : 413 → 419 avec PR-38 (6, comptes réciproques intragroupe : même forme que AX-15, finalité inverse).]
  [D-ED-8 et D-ED-9, 29/09/2026 : 393 → 413 avec PR-36 (12, raccord registre augmenté ↔ écriture duale)
   et PR-37 (8, registre d'un milieu déclaré par les concernés, portant le maintien).]
  [D-ED, 29/09/2026 : 377 → 393 avec PR-35 (16, écriture duale entre teneurs, N2).
   Renommages sans changement de preuve : EcritureDuale → RegistreComptableAugmente ;
   ecriture_duale_{preserve_R1, coherente, non_equivalence} → registre_augmente_{…, coherent, …} ;
   miroir_inter_acteurs_est_une_ecriture_duale → lien_inter_acteurs_porte_par_un_registre_augmente ;
   les_deux_ecritures_duales_ont_le_meme_socle → les_deux_registres_augmentes_ont_le_meme_socle.
   PR-31 `la_duale_exige_un_ancrage_par_cote` CONSERVÉ : « duale » y est au sens N2 (NT-ARCH §8.5).]
  [Critère de l'effet du défaut et P5, 28/09/2026 : 366 → 377 avec PR-33 (6) et PR-34 (5).]
  [C-9, 28/09/2026 : 361 → 366 avec PR-32 (5).]
  [Groupe C, 28/09/2026 : 328 → 361 avec PR-29 (10, dont 5 de texte), PR-30 (11), PR-31 (12).]
  [D-12, 28/09/2026 : 287 → 303 avec le versement de PR-26 (11) et PR-27 (5).]
  [D-13, 28/09/2026 : 303 → 317 avec les 14 témoins de non-vacuité ; renommage
   charge_de_preuve_declaree → sans_porteur_nomme_pas_de_renversement (D-13-4).]
  [B-5, 28/09/2026 : 317 → 315, retrait des deux théorèmes de V10b (forme 1), rattachés à CONV-2.]
  [NT-G2 §3.2, 28/09/2026 : 315 → 316, V1_commute_ssi_coherence.]
  [D-1, 28/09/2026 : 316 → 318, sonde étendue à la table §8.5.2 du 18/09 (audit A-4).]
  [D-5-2, 28/09/2026 : 318 → 317, retrait de PR4_ne_formalise_pas_l_appel_entendu.]
  [C-2/C-3, 28/09/2026 : 317 → 318 → 317, témoin inventaire_nonempty_discrimine (+1),
   retrait de la_forme_corrigee_n_a_pas_de_degre_de_liberte (−1).]
  [C-4 à C-14, 28/09/2026 : 317 → 312 ; six retraits (C-4, C-5, C-6, C-7, PR6 doublon C-12,
   C-14), un ajout (R1_systemique_ssi_creancier, C-13) ; trois renommages (C-8, C-9, C-10).]
  [R-7, 28/09/2026 : 312 → 315, trois témoins discriminants (PR-4, PR-20, PR-25) relevés
   manquants par la table nominative des lectures de fonctions.]
  [R-7 suite, 28/09/2026 : 315 → 317, deux témoins directs (PR-12, PR-23) remplaçant
   les témoins indirects n° 13 et n° 30 de la table.]
  [Relecture des 45 universels longs, 28/09/2026 : 317 → 318, témoin
   PR9_canalAE_temoin_discriminant ; V4c_actoriel_preserved déclaré forme 1.]
  [Conventions, 28/09/2026 : 318 → 328 ; CONV-7 au marqueur (PR-8 : renommage,
   +le_marqueur_se_leve_exactement_sur_le_defaut) ; PR-28, neuf ancrages (CONV-4, 6, 8, 14).]
  [D-10, 28/09/2026 : 286 → 287 avec `sans_mandat_borne_aucune_repartition`.]
  [D-11, 28/09/2026 : 285 → 286 avec `la_presence_produit_l_echappement`.]
  [A-8, 27/09/2026 : 286 → 285 si `PR24_ne_conclut_pas_P1` est retiré (forme 3).]
  (90 au 7 septembre ; 273 au 8 ; 286 au 9 septembre, après le
   versement de Sonde_PCEDed.lean — constat F7 de l'audit de
   découplage : un fichier du projet n'était ni construit ni audité.)
-/

import ProfReg

-- ─────────────────────────────────────────────────────────────
-- ProfReg/Interactions.lean  (2)
-- ─────────────────────────────────────────────────────────────
#print axioms exemple_sans_miroir_viole_R1
#print axioms systemique_sans_creancier_viole_R1
#print axioms R1_systemique_ssi_creancier

-- ─────────────────────────────────────────────────────────────
-- ProfReg/ChangeOfBase.lean  (4)
-- ─────────────────────────────────────────────────────────────
#print axioms CB1_in_unit
#print axioms CB1_lax_monoidal
#print axioms CB2_one
#print axioms CB2_zero

-- ─────────────────────────────────────────────────────────────
-- ProfReg/V2Verification.lean  (1)
-- ─────────────────────────────────────────────────────────────
#print axioms R1_preserved_under_CB1

-- ─────────────────────────────────────────────────────────────
-- ProfReg/CB3Attempt.lean  (1)
-- ─────────────────────────────────────────────────────────────
#print axioms CB3_candidate_not_oplax_monoidal

-- ─────────────────────────────────────────────────────────────
-- ProfReg/P2Synthesis.lean  (2)
-- ─────────────────────────────────────────────────────────────
#print axioms systemique_requires_R1_extension
#print axioms B1_coherence_condition

-- ─────────────────────────────────────────────────────────────
-- ProfReg/V1Verification.lean  (1)
-- ─────────────────────────────────────────────────────────────
#print axioms V1_commutatif
#print axioms V1_commute_ssi_coherence

-- ─────────────────────────────────────────────────────────────
-- ProfReg/V3Verification.lean  (3)
-- ─────────────────────────────────────────────────────────────
#print axioms ProfReg.V3_commutatif
#print axioms ProfReg.V3_aboutit_deliberation
#print axioms ProfReg.V3_actoriel_inchange

-- ─────────────────────────────────────────────────────────────
-- ProfReg/V4Verification.lean  (5)
-- ─────────────────────────────────────────────────────────────
#print axioms ProfReg.inventaire_nonempty_required
#print axioms ProfReg.inventaire_nonempty_discrimine
#print axioms ProfReg.cascade_deliberation_before_critique
#print axioms ProfReg.nonattribuee_force_deliberation
#print axioms ProfReg.critique_released_by_porteur
#print axioms ProfReg.V4_cascade_coherente

-- ─────────────────────────────────────────────────────────────
-- ProfReg/V4cVerification.lean  (3)
-- ─────────────────────────────────────────────────────────────
#print axioms V4c.V4c_actoriel_preserved
#print axioms V4c.V4c_regime_unchanged
#print axioms V4c.V4c_actoriel_preserved_alias

-- ─────────────────────────────────────────────────────────────
-- ProfReg/V10Verification.lean  (3)
-- ─────────────────────────────────────────────────────────────
#print axioms V10.V10a_planetaire_force_deliberation
#print axioms V10.V10a_planetaire_critique_interdit
#print axioms V10.V10a_synthese

-- ─────────────────────────────────────────────────────────────
-- ProfReg/V10bVerification.lean  (0 — B-5, 28/09/2026)
-- ─────────────────────────────────────────────────────────────
-- [B-5, 28/09/2026] V10b_triangle_commutatif et V10b_actoriel_stable retirés (forme 1) → CONV-2

-- ─────────────────────────────────────────────────────────────
-- ProfReg/VJEVerification.lean  (7)
-- ─────────────────────────────────────────────────────────────
#print axioms VJE.VJE_sensJE_declenche
#print axioms VJE.VJE_sensEJ_episodique
#print axioms VJE.VJE_sensEJ_structurel_bloque
#print axioms VJE.VJE_carre_ne_commute_pas_sans_revision
#print axioms VJE.VJE_ferme_apres_revision_externe
#print axioms VJE.sensJE_ne_produit_pas_la_revision
#print axioms VJE.VJE_pasDeJE_horsHermeneutique

-- ─────────────────────────────────────────────────────────────
-- ProfReg/LotL2_PR2_PR14.lean  (11)
-- ─────────────────────────────────────────────────────────────
#print axioms ProfRegLot.R1_preserved_under_base_change
#print axioms ProfRegLot.registre_augmente_preserve_R1
#print axioms ProfRegLot.registre_augmente_coherent
#print axioms ProfRegLot.registre_augmente_non_equivalence
#print axioms ProfRegLot.regime_declared_per_ecriture
#print axioms ProfRegLot.debit_actoriel_exclut_credit_systemique
#print axioms ProfRegLot.retiqueter_regime_unchanged
#print axioms ProfRegLot.fraction_exhibe_sa_source
#print axioms ProfRegLot.opposabilite_exige_statut_declare
#print axioms ProfRegLot.opposabilite_exhibe_statut
#print axioms ProfRegLot.PR14_ne_borne_pas_l_attribution

-- ─────────────────────────────────────────────────────────────
-- ProfReg/PR15_ChargeDePreuve.lean  (4)
-- ─────────────────────────────────────────────────────────────
#print axioms ProfRegD4.sans_porteur_nomme_pas_de_renversement
#print axioms ProfRegD4.preuve_non_reconstructible_ne_satisfait_pas
#print axioms ProfRegD4.charge_ne_retombe_pas_sur_les_affectes
#print axioms ProfRegD4.charge_satisfaite_et_renversement_declare_coexistent

-- ─────────────────────────────────────────────────────────────
-- ProfReg/PR10_StatutSeuil.lean  (8)
-- ─────────────────────────────────────────────────────────────
#print axioms ProfRegPR10.seuil_valuatif_must_declare_status
#print axioms ProfRegPR10.mixte_traite_comme_seuil_valuatif
#print axioms ProfRegPR10.PR10_ne_vaut_pas_pour_les_relationnelles
#print axioms ProfRegPR10.typage_binaire_apres_prudence
#print axioms ProfRegPR10.suspension_ni_absence_ni_endossement
#print axioms ProfRegPR10.suspension_ne_declenche_aucune_regle
#print axioms ProfRegPR10.orthogonalite_charge_valuative_usage
#print axioms ProfRegPR10.PR10_ne_prouve_pas_la_separabilite

-- ─────────────────────────────────────────────────────────────
-- ProfReg/PR3_AttributionSeuil.lean  (14)
-- ─────────────────────────────────────────────────────────────
#print axioms ProfRegPR3.attribuee_seuil_declare_required
#print axioms ProfRegPR3.attribution_exige_un_seuil_declare
#print axioms ProfRegPR3.stricte_est_instance_du_repli
#print axioms ProfRegPR3.repli_a_l_instant_d_attribution_est_strict
#print axioms ProfRegPR3.repli_sans_echeance_degenere
#print axioms ProfRegPR3.echeance_nommee_exige_une_date
#print axioms ProfRegPR3.stricte_interdit_declaration_posterieure
#print axioms ProfRegPR3.repli_autorise_l_attribution_avant_declaration
#print axioms ProfRegPR3.critique_exige_attribution
#print axioms ProfRegPR3.seuil_non_declare_interdit_attribution
#print axioms ProfRegPR3.seuil_non_declare_bloque_critique
#print axioms ProfRegPR3.attribution_exige_seuil_et_quadruplet
#print axioms ProfRegPR3.PR3_ne_departage_pas_les_seuils
#print axioms ProfRegPR3.PR3_ne_choisit_pas_le_regime

-- ─────────────────────────────────────────────────────────────
-- ProfReg/PR8_RefutationPratique.lean  (8)
-- ─────────────────────────────────────────────────────────────
#print axioms ProfRegPR8.representation_pratique_refutation
#print axioms ProfRegPR8.representation_planetaire_refutation
#print axioms ProfRegPR8.bien_formee_sans_refutation_n_est_pas_obligee
#print axioms ProfRegPR8.le_marqueur_se_leve_exactement_sur_le_defaut
#print axioms ProfRegPR8.planetaire_sans_porteur_exige_refutation
#print axioms ProfRegPR8.le_defaut_exige_la_refutation
#print axioms ProfRegPR8.exactement_deux_regimes_obliges
#print axioms ProfRegPR8.PR8_ne_vaut_pas_pour_les_legitimites_procedurales
#print axioms ProfRegPR8.PR8_ne_juge_pas_la_praticabilite

-- ─────────────────────────────────────────────────────────────
-- ProfReg/PR16_RefutationTiers.lean  (11)
-- ─────────────────────────────────────────────────────────────
#print axioms ProfRegPR16.refutation_exige_un_tiers
#print axioms ProfRegPR16.autorefutation_n_est_pas_refutation
#print axioms ProfRegPR16.refutation_exige_un_lieu
#print axioms ProfRegPR16.refutation_exige_une_reprise
#print axioms ProfRegPR16.PR8_ne_suffit_pas
#print axioms ProfRegPR16.le_foldr_max
#print axioms ProfRegPR16.nat_non_enumerable
#print axioms ProfRegPR16.liste_close_exclut_toujours
#print axioms ProfRegPR16.ouverture_n_exclut_personne
#print axioms ProfRegPR16.PR16_ne_designe_pas_le_tiers
#print axioms ProfRegPR16.une_inscription_bien_formee_porte_une_condition

-- ── Lot du 8 septembre 2026 — PR-17, PR-18, PR-19 ──────────────────
#print axioms ProfRegPR17.regime_du_dispositif_declare
#print axioms ProfRegPR17.experimentation_ne_supporte_pas_le_critere
#print axioms ProfRegPR17.nonDeclare_ne_vaut_pas_permission
#print axioms ProfRegPR17.PR17_admet_l_infrastructure
#print axioms ProfRegPR17.PR17_refuse_l_experimentation
#print axioms ProfRegPR17.PR17_n_interdit_pas_la_mesure
#print axioms ProfRegPR17.les_deux_mesures_ne_coincident_pas
#print axioms ProfRegPR18.porteur_du_seuil_exhibe_sa_population
#print axioms ProfRegPR18.cas_concernes
#print axioms ProfRegPR18.cas_tiers
#print axioms ProfRegPR18.declarant_seul_refutant_est_mal_formee
#print axioms ProfRegPR18.declarer_par_les_concernes_reste_admissible
#print axioms ProfRegPR18.PR18_n_impose_pas_qui_declare
#print axioms ProfRegPR18.PR18_ne_juge_pas_le_contenu
#print axioms ProfRegPR19.agreger_serieTriviale
#print axioms ProfRegPR19.serieTriviale_est_triviale
#print axioms ProfRegPR19.serie_bien_formee_agregat_non_conforme
#print axioms ProfRegPR19.serie_nulle_reste_conforme
#print axioms ProfRegPR19.seuil_nul_transfere_a_la_serie
#print axioms ProfRegPR19.PR19_n_interdit_aucune_serie
#print axioms ProfRegPR19.PR19_ne_juge_pas_le_seuil
#print axioms ProfRegPR19.PR19_ne_touche_pas_l_ecriture_isolee

-- ── Option D, 8 septembre 2026 — cinquième terme du statut du seuil ──
#print axioms ProfRegPR10.usage_agregat_non_declare_n_est_pas_une_declaration
#print axioms ProfRegPR10.BienFormee_ne_borne_pas_le_quintuplet
#print axioms ProfRegPR10.orthogonalite_usage_agregat_regime_usage
#print axioms ProfRegPR10.constatation_reste_licite
#print axioms ProfRegPR10.PR10_ne_juge_pas_l_usage_de_l_agregat
#print axioms ProfRegPR10.le_cinquieme_terme_ne_touche_pas_au_seuil

-- ── PR-20, 8 septembre 2026 — moitié inter-acteurs de P-C-E-D-e-d ──
#print axioms ProfRegPR20.lien_est_symetrique
#print axioms ProfRegPR20.la_creance_n_est_pas_symetrique
#print axioms ProfRegPR20.compat_financier
#print axioms ProfRegPR20.compat_communalite
#print axioms ProfRegPR20.lien_inter_acteurs_porte_par_un_registre_augmente
#print axioms ProfRegPR20.R1_tient_dans_les_deux_registres
#print axioms ProfRegPR20.roles_opposes
#print axioms ProfRegPR20.le_typage_determine_le_role
#print axioms ProfRegPR20.compat_financier_bis
#print axioms ProfRegPR20.accord_sur_l_existence_pas_sur_la_valeur
#print axioms ProfRegPR20.sans_creance_aucun_lien
#print axioms ProfRegPR20.absence_n_est_pas_lien_nul
#print axioms ProfRegPR20.miroirIA_involutive
#print axioms ProfRegPR20.miroirIA_sans_point_fixe
#print axioms ProfRegPR20.PR20_ne_designe_pas_le_creancier
#print axioms ProfRegPR20.sans_creance_sur_soi_pas_de_lien_a_soi
#print axioms ProfRegPR20.les_deux_registres_augmentes_ont_le_meme_socle
#print axioms ProfRegPR20.lien_temoin_discriminant

-- ── PR-21, 8 septembre 2026 — cinquième forme : le champ qui double un calcul ──
#print axioms ProfRegPR21.champ_declare_peut_mentir
#print axioms ProfRegPR21.les_deux_mensonges_existent
#print axioms ProfRegPR21.le_champ_ajoute_un_degre_de_liberte
#print axioms ProfRegPR21.controleR1_trie
#print axioms ProfRegPR21.respect_R1_peut_mentir
#print axioms ProfRegPR21.PR21_ne_condamne_pas_les_champs_declares
#print axioms ProfRegPR21.PR21_ne_juge_pas_le_controle
#print axioms ProfRegPR21.PR21_ne_dit_pas_que_la_fiche_ment

-- ── PR-22, 8 septembre 2026 — décision 1 de 12ter : P+C remonte en couche R ──
#print axioms ProfRegPR22.une_chose_deux_natures
#print axioms ProfRegPR22.enumeration_close_exclut_un_collectif
#print axioms ProfRegPR22.seule_l_ouverture_admet_tout_collectif
#print axioms ProfRegPR22.une_liste_close_de_collectifs_Nat_exclut_quelqu_un
#print axioms ProfRegPR22.PR22_ne_departage_pas_les_regimes
#print axioms ProfRegPR22.PR22_ne_supprime_pas_les_regimes_etablis
#print axioms ProfRegPR22.PR22_ne_calcule_aucun_miroir

-- ── PR-23, 8 septembre 2026 — appui formel de CONV-11 (décision 3 de 12ter) ──
#print axioms ProfRegPR23.BienFormee_ne_borne_pas_le_maintien
#print axioms ProfRegPR23.CONV11_est_satisfiable
#print axioms ProfRegPR23.deux_dettes_distinctes_meme_ecriture
#print axioms ProfRegPR23.la_glose_ne_rend_rien_lisible
#print axioms ProfRegPR23.ecart_lisible_temoin_discriminant
#print axioms ProfRegPR23.la_glose_varie_librement
#print axioms ProfRegPR23.priorite_sans_assiette
#print axioms ProfRegPR23.le_maintien_separe_les_situations
#print axioms ProfRegPR23.priorite_mord_si_inscrite
#print axioms ProfRegPR23.CONV11_satisfaite_sans_registre_financier
#print axioms ProfRegPR23.la_glose_ne_satisfait_pas_CONV11
#print axioms ProfRegPR23.PR23_ne_juge_aucun_montant
#print axioms ProfRegPR23.PR23_ne_privilegie_aucun_registre
#print axioms ProfRegPR23.PR23_n_affirme_aucune_dette
#print axioms ProfRegPR23.PR23_ne_certifie_pas_le_nommage
#print axioms ProfRegPR23.CONV11_complet_retrouve_PR23
#print axioms ProfRegPR23.CONV11_complet_satisfait_CONV11
#print axioms ProfRegPR23.la_projection_perd_la_contrepartie
#print axioms ProfRegPR23.la_dette_de_preservation_est_calculee

-- ── PR-11, 8 septembre 2026 — non-cessibilité (nœud NC, palier P6′) ──
#print axioms ProfRegPR11.obligation_non_cessible
#print axioms ProfRegPR11.porteur_stable_hors_devolution
#print axioms ProfRegPR11.seule_la_realisation_eteint
#print axioms ProfRegPR11.la_devolution_ne_solde_pas
#print axioms ProfRegPR11.l_effet_ne_distingue_pas_cession_et_devolution
#print axioms ProfRegPR11.l_etat_efface_son_origine
#print axioms ProfRegPR11.devolution_libre_reconstitue_la_cession
#print axioms ProfRegPR11.le_resultat_depend_du_regime
#print axioms ProfRegPR11.regime_strict_bloque_a_la_disparition
#print axioms ProfRegPR11.regime_strict_fige_le_porteur
#print axioms ProfRegPR11.PR11_n_interdit_pas_la_devolution
#print axioms ProfRegPR11.PR11_ne_choisit_pas_le_regime
#print axioms ProfRegPR11.PR11_ne_verifie_pas_la_realisation
#print axioms ProfRegPR11.PR11_ne_juge_pas_l_obligation

-- ── PR-13, 8 septembre 2026 — non-équivalence des niveaux (appui de CONV-12) ──
#print axioms ProfRegPR13.la_non_equivalence_est_calculee
#print axioms ProfRegPR13.sans_niveau_declare_aucun_verdict
#print axioms ProfRegPR13.aucune_fusion_entre_niveaux_distincts
#print axioms ProfRegPR13.niveau_non_declare_ne_vaut_pas_permission
#print axioms ProfRegPR13.niveau_non_declare_a_droite_ne_vaut_pas_permission
#print axioms ProfRegPR13.fusion_admise_seulement_au_meme_niveau
#print axioms ProfRegPR13.aucun_predicat_sur_la_charge_ne_borne_le_niveau
#print axioms ProfRegPR13.sans_le_niveau_l_interdiction_est_inapplicable
#print axioms ProfRegPR13.le_niveau_declare_separe_les_situations
#print axioms ProfRegPR13.controleNonEquivalence_trie
#print axioms ProfRegPR13.un_champ_non_equivalence_declare_pourrait_mentir
#print axioms ProfRegPR13.le_mensonge_sur_les_niveaux_irait_dans_les_deux_sens
#print axioms ProfRegPR13.la_fusion_au_meme_niveau_somme_les_charges
#print axioms ProfRegPR13.PR13_ne_hierarchise_pas_les_niveaux
#print axioms ProfRegPR13.PR13_n_interdit_pas_le_meme_niveau
#print axioms ProfRegPR13.entite_et_territoire_ne_fusionnent_pas

-- ── PR-6, 8 septembre 2026 — biconditionnelle AM-G7-04 fermée ──
#print axioms VJE.VJE_sansResistance
#print axioms VJE.VJE_sansResistance_sourceDID
#print axioms VJE.VJE_metalucidite_ssi
#print axioms VJE.VJE_source_ssi_metalucidite

-- ── PR-12 — non-confusion AX-2 / AX-3 (décisions 12.1-12.3), 8 septembre 2026 ──
#print axioms ProfRegPR12.l_obligation_A2_ne_se_repartit_pas
#print axioms ProfRegPR12.la_charge_A3_ne_se_renouvelle_pas
#print axioms ProfRegPR12.les_deux_erreurs_sont_symetriques
#print axioms ProfRegPR12.regime_non_declare_ne_vaut_pas_permission
#print axioms ProfRegPR12.traitement_admis_suppose_son_regime
#print axioms ProfRegPR12.sans_resultat_utile_aucune_repartition
#print axioms ProfRegPR12.sans_mandat_borne_aucune_repartition
#print axioms ProfRegPR12.le_signal_se_leve_exactement_sur_la_confusion
#print axioms ProfRegPR12.le_silence_n_est_pas_une_confusion
#print axioms ProfRegPR12.confusion_temoin_discriminant
#print axioms ProfRegPR12.controleConfusion_trie
#print axioms ProfRegPR12.un_signal_declare_pourrait_mentir
#print axioms ProfRegPR12.le_mensonge_irait_dans_les_deux_sens
#print axioms ProfRegPR12.PR12_ne_qualifie_aucune_dette
#print axioms ProfRegPR12.PR12_ne_juge_pas_le_montant
#print axioms ProfRegPR12.PR12_ne_hierarchise_pas
#print axioms ProfRegPR12.traitement_admis_laisse_la_dette_inchangee

-- ── PR-7 — R-PRIORITE-F6-F10, 8 septembre 2026 ──
#print axioms ProfRegPR7.F10_ne_certifie_pas_sous_F6_actif
#print axioms ProfRegPR7.traiter_F6_est_toujours_admis
#print axioms ProfRegPR7.F10_reprend_apres_traitement
#print axioms ProfRegPR7.la_coactivation_a_un_ordre_unique
#print axioms ProfRegPR7.la_priorite_n_est_pas_un_veto
#print axioms ProfRegPR7.PR7_ne_touche_pas_au_contenu
#print axioms ProfRegPR7.PR7_ne_juge_pas_l_injustice
#print axioms ProfRegPR7.PR7_ne_contraint_pas_hors_coactivation

-- ── PR-4 — déclenchement par le milieu, 8 septembre 2026 ──
#print axioms ProfRegPR4.milieu_degrade_persistant_declenche
#print axioms ProfRegPR4.un_seul_intervalle_ne_declenche_pas
#print axioms ProfRegPR4.cloture_declenchee_exhibe_un_inventaire_non_vide
#print axioms ProfRegPR4.le_type_ne_produit_aucun_inventaire
#print axioms ProfRegPR4.cloture_interdite_sans_inventaire
#print axioms ProfRegPR4.le_milieu_declenche_sans_qu_aucun_acteur_ait_declare
#print axioms ProfRegPR4.PR4_les_trois_declencheurs_suffisent_chacun
#print axioms ProfRegPR4.PR4_ne_juge_pas_le_contenu
#print axioms ProfRegPR4.PR4_temoin_discriminant
-- [D-5-2, 28/09/2026] PR4_ne_formalise_pas_l_appel_entendu retiré (forme 1, doublon)

-- ── PR-9 — canal E→A : le couplage est un cycle, la condition est la terminaison, 8 septembre 2026 ──
#print axioms ProfRegPR9.le_couplage_est_un_cycle
#print axioms ProfRegPR9.les_deux_ordres_different
#print axioms ProfRegPR9.un_canal_qui_ne_relit_pas_le_seuil_termine
#print axioms ProfRegPR9.un_canal_qui_relit_le_seuil_ne_termine_pas
#print axioms ProfRegPR9.la_terminaison_se_verifie_sur_le_canal_seul
#print axioms ProfRegPR9.PR9_n_instrumente_pas_le_canal
#print axioms ProfRegPR9.PR9_ne_supprime_pas_le_canal_AE
#print axioms ProfRegPR9.PR9_canalAE_temoin_discriminant
#print axioms ProfRegPR9.PR9_ne_juge_pas_le_seuil

-- ── PR-5 — carré M↔R : il ne commute pas, un acte le ferme, 8 septembre 2026 ──
#print axioms ProfRegPR5.le_carre_MR_ne_commute_pas
#print axioms ProfRegPR5.l_ordre_RM_puis_MR_inscrit_seul
#print axioms ProfRegPR5.aucun_sens_ne_produit_la_voix
#print axioms ProfRegPR5.aucun_sens_ne_produit_l_audit
#print axioms ProfRegPR5.le_carre_ferme_apres_l_acte
#print axioms ProfRegPR5.un_seul_des_deux_actes_ne_ferme_pas
#print axioms ProfRegPR5.PR5_ne_refute_pas_le_couplage
#print axioms ProfRegPR5.PR5_ne_juge_pas_la_meconnaissance

-- ── PR-24 — portée finie, premier appui formel de P1 (maillon L1), 8 septembre 2026 ──
#print axioms ProfRegPR24.la_presence_exclut_toujours
#print axioms ProfRegPR24.l_inscription_exclut_aussi
#print axioms ProfRegPR24.l_inscription_est_monotone
#print axioms ProfRegPR24.la_presence_perd_ce_que_l_inscription_garde
#print axioms ProfRegPR24.le_soin_en_presence_se_perd
#print axioms ProfRegPR24.la_presence_produit_l_echappement
#print axioms ProfRegPR24.PR24_ne_dit_pas_que_le_registre_suffit
#print axioms ProfRegPR24.PR24_l_exclusion_est_conditionnelle
#print axioms ProfRegPR24.meme_presence_inscriptions_differentes

-- ── PR-25 — vérification sans divulgation, appui formel de P5, 8 septembre 2026 ──
#print axioms ProfRegPR25.la_lecture_com_decide_le_lien
#print axioms ProfRegPR25.les_deux_observateurs_concluent_pareil
#print axioms ProfRegPR25.la_symetrie_reste_lisible_en_acces_limite
#print axioms ProfRegPR25.l_inscription_financiere_du_lien_n_est_pas_divulguee
#print axioms ProfRegPR25.les_deux_temoins_sont_coherents
#print axioms ProfRegPR25.PR25_n_etablit_aucune_confidentialite
#print axioms ProfRegPR25.PR25_ne_verifie_que_l_existence
#print axioms ProfRegPR25.PR25_n_exige_aucune_harmonisation
#print axioms ProfRegPR25.la_lecture_com_temoin_discriminant

-- ─────────────────────────────────────────────────────────────
-- ProfReg/Sonde_PCEDed.lean  (15 — D-1, 28/09/2026 : +2 sur la table du 18/09)
-- Versée le 9 septembre 2026 (lot 10). Formalise le TEXTE de
-- NT-ARCH §8.5 tel qu'il était le 8 septembre, avant les décisions
-- 1/2/3 de 12ter — voir l'avertissement d'antériorité en tête du
-- fichier. Aucun de ces théorèmes n'établit une thèse du MRC.
-- ─────────────────────────────────────────────────────────────
#print axioms SondePCEDed.E_plus_admet_le_vide
#print axioms SondePCEDed.seul_E_plus_admet_le_vide
#print axioms SondePCEDed.engagement_sans_miroir_n_est_pas_dette_sans_creancier
#print axioms SondePCEDed.couple_symetrique_C_D
#print axioms SondePCEDed.couple_asymetrique_P_e
#print axioms SondePCEDed.la_table_melange_deux_relations
#print axioms SondePCEDed.second_couple_asymetrique
#print axioms SondePCEDed.respect_R1_declare_peut_mentir
#print axioms SondePCEDed.respect_R1_declare_peut_se_sous_estimer
#print axioms SondePCEDed.composites_bien_types
#print axioms SondePCEDed.miroir_non_defini_sur_les_composites
#print axioms SondePCEDed.la_sonde_ne_condamne_pas_le_typage
#print axioms SondePCEDed.la_sonde_ne_tranche_pas
#print axioms SondePCEDed.seul_E_plus_admet_le_vide_table_1809
#print axioms SondePCEDed.les_resultats_de_la_sonde_tiennent_table_1809

-- ── PR-26 — second axe d'extinction (NT-ARCH §4bis), versé le 28/09/2026 (D-12) ──
#print axioms ProfRegPR26.le_silence_ne_solde_rien
#print axioms ProfRegPR26.deux_regimes_divergents_ne_suffisent_pas
#print axioms ProfRegPR26.le_tiers_atteste_leve_le_refus
#print axioms ProfRegPR26.l_extinction_ne_depend_pas_de_l_attribution
#print axioms ProfRegPR26.la_machine_d_attribution_ignore_l_extinction
#print axioms ProfRegPR26.seul_debiteur_bien_forme_mais_marque
#print axioms ProfRegPR26.le_miroir_des_concernes_leve_le_marqueur
#print axioms ProfRegPR26.une_extinction_bien_formee_peut_etre_une_remise
#print axioms ProfRegPR26.tiers_lemme_sans_critere_mal_forme
#print axioms ProfRegPR26.une_dette_A2_ne_s_eteint_jamais
#print axioms ProfRegPR26.le_quart_lemme_est_le_regime_de_A2

-- ── PR-27 — candidats de septembre (AX-3, CONV-4, CONV-14), versé le 28/09/2026 (D-12) ──
#print axioms ProfRegPR27.PR12_coincide_avec_la_fiche
#print axioms ProfRegPR27.l_avarie_qualifiee_ne_suffit_pas
#print axioms ProfRegPR27.le_repartiteur_non_nomme_ne_decouple_pas
#print axioms ProfRegPR27.fraction_exhibe_une_source_eventuellement_vide
#print axioms ProfRegPR27.le_score_ne_determine_pas_les_axes

-- D-13 — témoins de non-vacuité (NT-ARCH §8ter-bis, R-2), 28/09/2026 (14)
#print axioms ProfRegLot.PR14_temoin_mal_forme
#print axioms ProfRegLot.PR2_PaireHomogene_discrimine
#print axioms ProfRegPR10.PR10_clause1_temoin_mal_forme
#print axioms ProfRegPR10.PR10_suspension_temoin_mal_forme
#print axioms ProfRegPR3.PR3_clauseSeuil_temoin_mal_forme
#print axioms ProfRegPR8.PR8_temoin_mal_forme
#print axioms ProfRegPR8.PR8_RegleAM_discrimine
#print axioms ProfRegD4.PR15_discrimine
#print axioms ProfRegPR16.PR16_alterite_temoin_discriminant
#print axioms ProfRegPR16.PR16_moyens_temoin_discriminant
#print axioms ProfRegPR16.PR16_reprise_temoin_discriminant
#print axioms ProfRegPR18.PR18_temoin_mal_forme
#print axioms ProfRegPR27.PR27_temoin_bien_forme
#print axioms ProfRegPR28.nondeclare_force_deliberation
#print axioms ProfRegPR28.CONV8_temoin_discriminant
#print axioms ProfRegPR28.BienFormee_ne_borne_pas_la_prospective
#print axioms ProfRegPR28.CONV6_est_satisfiable
#print axioms ProfRegPR28.CONV6_ne_vaut_pas_dans_l_exercice
#print axioms ProfRegPR28.CONV4_satisfaite_sans_DID
#print axioms ProfRegPR28.source_sans_porteur_mal_formee
#print axioms ProfRegPR28.CONV4_ne_prescrit_aucune_forme
#print axioms ProfRegPR28.la_comparaison_sur_un_axe_n_est_pas_le_classement
#print axioms V1_coherence_discrimine

-- ── Groupe C (audit §3.2), versé le 28/09/2026 ──
-- PR-29 — table §8.5.2 : « + » composite, colonne dédoublée, arités (5 texte : les cinq premiers ; 5 architecture)
#print axioms ProfRegPR29.branches_fideles_a_la_table
#print axioms ProfRegPR29.la_colonne_d_origine_ne_satisfait_pas_B7
#print axioms ProfRegPR29.le_decompte_depend_de_la_lecture_du_plus
#print axioms ProfRegPR29.sous_la_colonne_dedoublee_restent_quatre_lacunes
#print axioms ProfRegPR29.le_dedoublement_conserve_la_contrepartie
#print axioms ProfRegPR29.absent_n_implique_pas_violation
#print axioms ProfRegPR29.le_statut_ne_se_lit_pas_sur_la_table
#print axioms ProfRegPR29.trois_livres_sans_tiers_mal_formee
#print axioms ProfRegPR29.trois_livres_temoin_discriminant
#print axioms ProfRegPR29.la_troisieme_arite_n_est_pas_la_deuxieme
-- PR-30 — communalité §8.5.6 (11)
#print axioms ProfRegPR30.la_branche_B_exclut_le_capital_d_apporteur
#print axioms ProfRegPR30.non_determinable_rend_indetermine
#print axioms ProfRegPR30.le_non_declare_ne_qualifie_pas_et_marque
#print axioms ProfRegPR30.qualifiant_temoin_discriminant
#print axioms ProfRegPR30.une_classe_non_repartissable_suffit
#print axioms ProfRegPR30.la_qualification_agregee_n_est_pas_la_qualification_par_classe
#print axioms ProfRegPR30.classe_manquante_rend_indetermine
#print axioms ProfRegPR30.la_completude_prime_sur_la_classe_qualifiante
#print axioms ProfRegPR30.citer_ses_regles_n_engage_pas_les_tiers
#print axioms ProfRegPR30.la_pratique_seule_marque_et_ne_qualifie_pas
#print axioms ProfRegPR30.droit_d_ecrire_n_est_pas_pouvoir_d_engager
-- PR-31 — bonne formation déclarative (16)
#print axioms ProfRegPR31.le_marqueur_de_milieu_se_leve_exactement_sur_l_interprete_manquant
#print axioms ProfRegPR31.trois_termes_temoin_discriminant
#print axioms ProfRegPR31.l_interprete_ne_se_deduit_pas_du_declarant
#print axioms ProfRegPR31.sans_ancrage_refusee
#print axioms ProfRegPR31.le_registre_de_communalite_suffit
#print axioms ProfRegPR31.la_duale_exige_un_ancrage_par_cote
#print axioms ProfRegPR31.ancree_duale_ssi
#print axioms ProfRegPR31.deux_comptabilites_tenues_ancrent_une_duale
#print axioms ProfRegPR31.le_registre_de_communalite_ancre_un_cote
#print axioms ProfRegPR31.un_seul_teneur_pas_de_duale
#print axioms ProfRegPR31.sans_objet_sans_motif_est_un_nondeclare_renomme
#print axioms ProfRegPR31.le_motif_refute_requalifie
#print axioms ProfRegPR31.G4_n_admet_pas_le_titulaire_non_humain
#print axioms ProfRegPR31.representant_sans_dimension_mal_forme
#print axioms ProfRegPR31.P7_temoin_discriminant
#print axioms ProfRegPR31.la_lecture_exclusive_ne_porte_pas_deux_dimensions
-- PR-32 — candidat de régime et horizon du marqueur CONV-7 (C-9, 28/09/2026) (5)
#print axioms ProfRegPR32.regime_sans_refutation_n_autorise_aucune_ecriture
#print axioms ProfRegPR32.candidat_ssi_critere_de_sortie_et_caducite
#print axioms ProfRegPR32.regime_temoin_discriminant
#print axioms ProfRegPR32.le_marqueur_a_toujours_un_horizon
#print axioms ProfRegPR32.marqueur_temoin_discriminant
-- PR-33 — effet du défaut : codes et critère ordonné (piste 7), 28/09/2026 (6)
#print axioms ProfRegPR33.classement_de_reference
#print axioms ProfRegPR33.l_ordre_fait_prevaloir_l_objet
#print axioms ProfRegPR33.l_inscription_dommageable_est_refusee_avant_tout_marqueur
#print axioms ProfRegPR33.mal_formee_n_implique_pas_refusee
#print axioms ProfRegPR33.les_refus_ne_viennent_que_des_branches_un_a_trois
#print axioms ProfRegPR33.le_marqueur_ne_vient_que_de_l_appreciation_ou_du_candidat
#print axioms ProfRegPR33.sans_branche_pas_de_classement
-- PR-34 — instrument-hôte (P5), 28/09/2026 (5)
#print axioms ProfRegPR34.hote_non_declare_delibere
#print axioms ProfRegPR34.la_voie_intermediaire_ne_dispense_pas_du_triplet
#print axioms ProfRegPR34.P5_temoin_discriminant
#print axioms ProfRegPR34.sans_gouvernance_declaree_le_marqueur_suffit
#print axioms ProfRegPR34.P5_suit_le_critere
-- PR-35 — écriture duale entre teneurs (N2), ancrage banque/client, 29/09/2026 (16)
#print axioms ProfRegPR35.filtre_vide_de_tous_faux
#print axioms ProfRegPR35.tous_faux_de_filtre_vide
#print axioms ProfRegPR35.ecriture_duale_ssi_rapprochement_vide
#print axioms ProfRegPR35.ecriture_duale_symetrique
#print axioms ProfRegPR35.le_miroir_change_de_role
#print axioms ProfRegPR35.la_ligne_miroir_est_de_role_oppose
#print axioms ProfRegPR35.pret_bancaire_est_une_ecriture_duale
#print axioms ProfRegPR35.l_ecriture_duale_peut_echouer
#print axioms ProfRegPR35.l_etat_de_rapprochement_nomme_l_ecart
#print axioms ProfRegPR35.le_rapprochement_resorbe_l_ecart
#print axioms ProfRegPR35.le_rapprochement_ne_resorbe_qu_un_sens
#print axioms ProfRegPR35.pret_bancaire_concordant
#print axioms ProfRegPR35.duale_n_implique_pas_concordante
#print axioms ProfRegPR35.concordante_implique_duale
#print axioms ProfRegPR35.ecriture_duale_temoin_discriminant
#print axioms ProfRegPR35.deux_silences_sont_en_ecriture_duale
-- PR-36 — raccord N3 ↔ N2 (D-ED-8), 29/09/2026 (12)
#print axioms ProfRegPR36.nat_beq_refl
#print axioms ProfRegPR36.nat_eq_of_beq
#print axioms ProfRegPR36.versActeur_de_ligne
#print axioms ProfRegPR36.aUneLigneVers_iff
#print axioms ProfRegPR36.coherent_vers_acteur
#print axioms ProfRegPR36.le_registre_tenu_satisfait_L2
#print axioms ProfRegPR36.raccord_augmente_duale
#print axioms ProfRegPR36.raccord_temoin
#print axioms ProfRegPR36.sans_coherence_pas_de_raccord
#print axioms ProfRegPR36.sans_duale_pas_de_raccord
#print axioms ProfRegPR36.le_raccord_ne_porte_pas_la_valeur
#print axioms ProfRegPR36.coherent_temoin_discriminant
-- PR-37 — registre d'un milieu ou d'un collectif (D-ED-9 ; révisé D-ED-16 et D-ED-14, 30/09/2026) (16)
#print axioms ProfRegPR37.sans_registre_l_ecart_reste_inscrit
#print axioms ProfRegPR37.la_ratification_ne_fonde_pas_le_registre
#print axioms ProfRegPR37.sans_declaration_pas_de_registre
#print axioms ProfRegPR37.sans_critere_d_inclusion_pas_de_registre
#print axioms ProfRegPR37.sans_interprete_pas_de_registre
#print axioms ProfRegPR37.sans_interprete_le_marqueur_PR31_se_leve
#print axioms ProfRegPR37.sans_maintien_pas_d_appui
#print axioms ProfRegPR37.maintien_d_un_autre_registre_pas_d_appui
#print axioms ProfRegPR37.le_milieu_n_ecrit_pas_son_registre
#print axioms ProfRegPR37.ecriture_duale_avec_un_milieu
#print axioms ProfRegPR37.registre_de_milieu_temoin_discriminant
#print axioms ProfRegPR37.declaration_echue_l_ecart_revient
#print axioms ProfRegPR37.l_interprete_n_est_pas_un_concerne
#print axioms ProfRegPR37.registre_mal_nomme_l_ecart_revient
#print axioms ProfRegPR37.la_dette_de_preservation_du_milieu_est_calculee
#print axioms ProfRegPR37.un_collectif_peut_tenir_son_propre_registre
-- PR-38 — comptes réciproques intragroupe (D-ED-10), 30/09/2026 (6 +1 D-ED-37 = 7)
#print axioms ProfRegPR38.role_miroir
#print axioms ProfRegPR38.une_paire_concordante_s_annule
#print axioms ProfRegPR38.le_pret_intragroupe_a_la_forme_de_A15
#print axioms ProfRegPR38.la_consolidation_efface_ce_que_l_ecriture_duale_conserve
#print axioms ProfRegPR38.la_consolidation_efface_toujours_la_paire  -- D-ED-37, forme générale
#print axioms ProfRegPR38.sans_concordance_l_elimination_laisse_un_ecart
#print axioms ProfRegPR38.l_addition_est_possible_mais_non_prescrite
-- PR-39 — réalisation du maintien (D-ED-15), 30/09/2026 (7)
#print axioms ProfRegPR39.sans_constat_rien_n_est_decharge
#print axioms ProfRegPR39.le_constat_ramene_a_la_dette_de_preservation
#print axioms ProfRegPR39.attendu_n_est_pas_constate
#print axioms ProfRegPR39.l_auto_constat_ne_vaut_pas
#print axioms ProfRegPR39.la_contestation_est_inscrite
#print axioms ProfRegPR39.non_reconduit_revient_en_attente
#print axioms ProfRegPR39.etat_temoin_discriminant
-- PR-40 — statut de l'écart (D-ED-13), 30/09/2026 (6)
#print axioms ProfRegPR40.la_communication_ne_change_pas_l_ecart
#print axioms ProfRegPR40.en_ecriture_duale_rien_a_qualifier
#print axioms ProfRegPR40.non_verifiable_n_est_pas_constate
#print axioms ProfRegPR40.le_refus_n_est_pas_un_silence
#print axioms ProfRegPR40.la_denegation_rend_l_ecart_conteste
#print axioms ProfRegPR40.statut_temoin_discriminant
-- PR-41 — arbitrage de l'écart par un tiers (D-ED-12), 30/09/2026 (6)
#print axioms ProfRegPR41.aucun_teneur_ne_tranche
#print axioms ProfRegPR41.un_tiers_lie_ne_tranche_pas
#print axioms ProfRegPR41.l_arbitrage_n_efface_rien
#print axioms ProfRegPR41.le_tiers_tranche_la_contestation
#print axioms ProfRegPR41.l_infirmation_laisse_la_ligne_inscrite
#print axioms ProfRegPR41.arbitrer_temoin_discriminant
-- PR-42 — teneurs indépendants (D-ED-17), 30/09/2026 (7)
#print axioms ProfRegPR42.probante_suppose_la_duale
#print axioms ProfRegPR42.entre_lies_sans_tiers_rien_ne_prouve
#print axioms ProfRegPR42.sous_controle_la_duale_ne_prouve_pas_seule
#print axioms ProfRegPR42.un_temoin_du_groupe_ne_suffit_pas
#print axioms ProfRegPR42.entre_independants_la_duale_suffit
#print axioms ProfRegPR42.sous_subordination_meme_regle
#print axioms ProfRegPR42.probante_temoin_discriminant
-- PR-43 — instance de contrôle (D-ED-20, CONV-16), 30/09/2026 (7 +1 D-ED-37 = 8)
#print axioms ProfRegPR43.sans_instance_commune_rien_n_est_arbitre
#print axioms ProfRegPR43.l_instance_liee_n_arbitre_pas
#print axioms ProfRegPR43.seule_l_instance_commune_tranche
#print axioms ProfRegPR43.l_instance_commune_tranche_toujours  -- D-ED-37, forme générale
#print axioms ProfRegPR43.la_designation_doit_etre_commune_et_arretee
#print axioms ProfRegPR43.l_instance_ne_peut_etre_partie
#print axioms ProfRegPR43.l_instance_de_controle_peut_constater
#print axioms ProfRegPR43.instance_commune_temoin_discriminant
-- PR-44 — constat unilatéral : attestation interne, tiers extérieur (D-ED-21), 30/09/2026 (12 +1 D-ED-29 +1 D-ED-30 = 14)
#print axioms ProfRegPR44.le_parcours_n_efface_rien
#print axioms ProfRegPR44.sans_attestation_rien_n_est_porte
#print axioms ProfRegPR44.sans_consentement_la_voie_privee_est_fermee
#print axioms ProfRegPR44.la_voie_publique_ignore_le_refus
#print axioms ProfRegPR44.sans_piece_exterieure_pas_de_foi
#print axioms ProfRegPR44.au_penal_le_constat_renseigne
#print axioms ProfRegPR44.l_attestation_interne_ne_tranche_pas
#print axioms ProfRegPR44.le_refus_ne_ferme_que_la_voie_privee
#print axioms ProfRegPR44.le_juge_exige_la_qualite
#print axioms ProfRegPR44.la_transaction_suppose_x
#print axioms ProfRegPR44.la_piece_exterieure_fait_foi_au_civil
#print axioms ProfRegPR44.statut_constat_temoin_discriminant
#print axioms ProfRegPR44.l_arbitrage_exige_une_convention  -- D-ED-29
#print axioms ProfRegPR44.l_autorite_de_supervision_ne_depend_pas_de_la_societe  -- D-ED-30
-- PR-45 — protocole d'attestation, CONV-17, miroir reconstitué (D-ED-22, 23, 24), 30/09/2026 (9)
#print axioms ProfRegPR45.conv17_sans_protocole_hors_protocole
#print axioms ProfRegPR45.conv17_n_interdit_pas_de_signaler
#print axioms ProfRegPR45.conv17_avec_protocole_retrouve_PR44
#print axioms ProfRegPR45.la_reconstitution_suppose_un_detenteur_tiers
#print axioms ProfRegPR45.la_sous_declaration_est_chiffree
#print axioms ProfRegPR45.chaque_rubrique_compte
#print axioms ProfRegPR45.le_membre_signale_hors_registre
#print axioms ProfRegPR45.confronter_temoin_discriminant
#print axioms ProfRegPR45.conforme_temoin_discriminant
-- PR-46 — registre de chaîne, relation à trois parties (D-ED-18), 30/09/2026 (11 +1 D-ED-29 +1 D-ED-37 = 13)
#print axioms ProfRegPR46.directement_lie_pas_de_dette_de_reparation
#print axioms ProfRegPR46.exiger_n_endette_pas
#print axioms ProfRegPR46.la_projection_perd_le_fournisseur
#print axioms ProfRegPR46.plainte_fondee_ecart_resorbe
#print axioms ProfRegPR46.la_signature_vaut_consentement_ex_ante
#print axioms ProfRegPR46.la_signature_n_ouvre_pas_la_transaction  -- D-ED-29
#print axioms ProfRegPR46.l_etoile_porte_la_chaine
#print axioms ProfRegPR46.l_etoile_est_toujours_duale  -- D-ED-37, forme générale
#print axioms ProfRegPR46.l_objet_declare_borne_le_registre
#print axioms ProfRegPR46.pas_de_consolidation_dans_la_chaine
#print axioms ProfRegPR46.le_teneur_n_est_pas_l_instance
#print axioms ProfRegPR46.la_plainte_fondee_force_le_miroir
#print axioms ProfRegPR46.qualifier_temoin_discriminant
-- PR-47 — CONV-18, annotation de destination (D-ED-27), 30/09/2026 (6)
#print axioms ProfRegPR47.sans_site_destination_non_declaree
#print axioms ProfRegPR47.le_lien_retenu_prime
#print axioms ProfRegPR47.l_instance_requalifie_le_lien
#print axioms ProfRegPR47.un_verificateur_non_designe_ne_vaut_pas
#print axioms ProfRegPR47.destination_infirmee_et_objet_hors_registre
#print axioms ProfRegPR47.etat18_temoin_discriminant
-- PR-48 — qualification des plaintes (D-ED-30), 30/09/2026 (7)
#print axioms ProfRegPR48.non_fondee_est_une_contestation
#print axioms ProfRegPR48.plainte_retenue_miroir_force
#print axioms ProfRegPR48.plainte_non_retenue_rien_ne_change
#print axioms ProfRegPR48.la_societe_ne_s_arbitre_pas
#print axioms ProfRegPR48.sans_instance_l_autorite
#print axioms ProfRegPR48.le_miroir_force_sur_l_instance
#print axioms ProfRegPR48.issue_plainte_temoin_discriminant
-- PR-49 — garde de forme et injonction de vigilance (D-ED-34, D-ED-35), 30/09/2026 (7)
#print axioms ProfRegPR49.la_conformite_ne_vaut_pas_realisation
#print axioms ProfRegPR49.conformite_et_realisation_independantes
#print axioms ProfRegPR49.sans_mise_en_demeure_irrecevable
#print axioms ProfRegPR49.avant_trois_mois_irrecevable
#print axioms ProfRegPR49.la_lecture_stricte_ferme_ce_que_la_souple_ouvre
#print axioms ProfRegPR49.sans_interet_a_agir_irrecevable
#print axioms ProfRegPR49.injonction_temoin_discriminant
-- PR-50 — forme du signal carre_non_commutatif (F3) : deux chemins, écart déclaré, seuil déclaré, 02/10/2026 (7)
#print axioms ProfRegPR50.signal_implique_non_commutation
#print axioms ProfRegPR50.commutatif_ne_signale_pas
#print axioms ProfRegPR50.seuil_non_declare_ne_signale_pas
#print axioms ProfRegPR50.non_commutation_sous_le_seuil_ne_signale_pas
#print axioms ProfRegPR50.signal_temoin_discriminant
#print axioms ProfRegPR50.le_signal_depend_de_l_ecart_declare
#print axioms ProfRegPR50.action_temoin_discriminant
#print axioms ProfRegPR51.le_chemin_direct_n_est_pas_admissible
#print axioms ProfRegPR51.entrer_en_deliberation_exige_l_inventaire
#print axioms ProfRegPR51.aucune_deliberation_sans_inventaire
#print axioms ProfRegPR51.carre_B1B2_commute_sur_les_chemins_admissibles
#print axioms ProfRegPR51.carre_temoin_discriminant
#print axioms ProfRegPR51.le_carre_a_un_chemin_admissible
#print axioms ProfRegPR52.sans_source_rien_n_est_legitime
#print axioms ProfRegPR52.la_source_ne_suffit_pas
#print axioms ProfRegPR52.noncollecte_n_est_jamais_legitime
#print axioms ProfRegPR52.sur_support_distribue_rien_n_est_inscriptible
#print axioms ProfRegPR52.inscriptible_temoin_discriminant
#print axioms ProfRegPR52.la_souffrance_seule_ne_qualifie_aucune_creance
#print axioms ProfRegPR52.la_souffrance_n_empeche_pas_la_qualification
#print axioms ProfRegPR53.le_filtre_n_ecarte_que_le_declare_incident
#print axioms ProfRegPR53.local_mais_structurel_passe
#print axioms ProfRegPR53.non_declare_passe_avec_marqueur
#print axioms ProfRegPR53.documentee_par_la_souffrance_ne_passe_pas
#print axioms ProfRegPR53.filtre_temoin_discriminant
#print axioms ProfRegPR53.l_hypothese_seule_ne_qualifie_pas_le_regime
#print axioms ProfRegPR53.le_cycle_AJ_termine
#print axioms ProfRegPR53.la_souffrance_ne_se_confirme_pas_elle_meme
#print axioms ProfRegPR53.declare_et_presume_s_excluent
#print axioms ProfRegPR53.deni_presume_temoin
#print axioms ProfRegPR53.ordre_non_respecte_deux_effets
#print axioms ProfRegPR54.boucle_confirmante_atteste_l_alignement
#print axioms ProfRegPR54.la_contre_performativite_ne_leve_pas_la_boucle
#print axioms ProfRegPR54.boucle_temoin_discriminant
#print axioms ProfRegPR54.l_effet_d_hote_voit_un_cas_contraire
#print axioms ProfRegPR54.hors_hote_la_contre_performativite_est_invisible
#print axioms ProfRegPR54.desalignement_sans_hote_temoin
#print axioms ProfRegPR54.le_registre_ne_lit_pas_l_hote_reel
#print axioms ProfRegPR54.un_hote_reel_declare_aucun_echappe
#print axioms ProfRegPR55.corpus_non_consenti_lit_le_mode_de_validation
#print axioms ProfRegPR55.corpus_signal_temoin_discriminant
#print axioms ProfRegPR55.la_representation_ne_couvre_pas_un_joignable
#print axioms ProfRegPR55.l_absence_n_est_jamais_un_verrou
#print axioms ProfRegPR55.les_deux_cles_sont_necessaires
#print axioms ProfRegPR55.le_changement_de_mode_ne_leve_pas
#print axioms ProfRegPR55.bloque_temoin_discriminant
#print axioms ProfRegPR56.le_consentement_du_corpus_est_derive
#print axioms ProfRegPR56.consentement_derive_temoin
#print axioms ProfRegPR56.sans_trace_ni_attestation_pas_d_absence
#print axioms ProfRegPR56.une_contestation_retenue_fait_tomber_la_representation
#print axioms ProfRegPR56.trace_ou_attestation_temoin
#print axioms ProfRegPR56.pr56_restreint_pr55
#print axioms ProfRegPR56.l_absence_opposable_n_est_jamais_un_verrou
#print axioms ProfRegPR57.non_instruit_ne_vaut_pas_aligne
#print axioms ProfRegPR57.le_porteur_ne_s_atteste_pas
#print axioms ProfRegPR57.sans_les_concernes_pas_de_constat
#print axioms ProfRegPR57.hypothese_apres_coup_non_admise
#print axioms ProfRegPR57.constat_temoin_discriminant
#print axioms ProfRegPR57.a_qualifier_relance_sans_signal
#print axioms ProfRegPR57.pas_de_relance_sans_constat
#print axioms ProfRegPR57.l_enquete_rend_visible_la_contre_performativite
#print axioms ProfRegPR57.sans_constat_la_lacune_demeure
#print axioms ProfRegPR57.echeance_sans_concernes_n_ouvre_pas
#print axioms ProfRegPR58.le_typage_est_necessaire
#print axioms ProfRegPR58.sans_instance_deliberative_pas_de_commun
#print axioms ProfRegPR58.sans_instance_de_controle_pas_de_commun
#print axioms ProfRegPR58.une_indivision_n_est_pas_un_commun
#print axioms ProfRegPR58.une_forme_admise_sans_deliberation_n_est_pas_un_commun
#print axioms ProfRegPR58.la_propriete_seule_n_est_jamais_un_commun
#print axioms ProfRegPR58.l_interet_diffus_se_passe_d_attributaire
#print axioms ProfRegPR58.commun_temoin_discriminant
#print axioms ProfRegPR58.l_interet_commun_ne_determine_pas_l_inclusivite
#print axioms ProfRegPR59.pas_d_alerte_sans_seuil_declare
#print axioms ProfRegPR59.non_instruit_n_est_pas_nul
#print axioms ProfRegPR59.un_cycle_ne_suffit_pas
#print axioms ProfRegPR59.meme_ecart_total_droits_differents
#print axioms ProfRegPR59.sans_faisceau_pas_d_alerte
#print axioms ProfRegPR59.l_inclusivite_du_controle_ne_determine_pas_l_interet_commun
#print axioms ProfRegPR59.controle_temoin
#print axioms ProfRegPR59.le_premier_sens_porte_sur_l_attributaire
