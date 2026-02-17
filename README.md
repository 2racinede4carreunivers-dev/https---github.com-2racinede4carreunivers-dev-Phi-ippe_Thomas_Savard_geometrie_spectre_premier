# 📑 Table des matières — Géométrie du Spectre Premier

## 1. Introduction générale
- Contexte et objectifs
- Structure des deux fichiers HOL
- Présentation des rapports spectraux (1/2, 1/3, 1/4)

---

# 🟦 PARTIE I — MÉTHODE DE PHILIPPOT

## 2. Suites négatives et équations spectrales
- SA_neg_eq, SB_neg_eq
- digamma_neg_calc
- Lemme de réécriture

## 3. Rapport spectral négatif 1/2
- Définition RsP_neg
- Axiomatisation
- Lemme général

## 4. Géométrie spectrale : asymétries
- indice_valide
- listes strictement croissantes
- asymétrie ordonnée
- asymétrie chaotique
- Lemme fondamental

## 5. Étape 1 : suites rationnelles explicites
- Suites 3 à 11 termes
- Fonction générale
- Structure réglementaire

## 6. Étape 2 : substitutions spectrales
- Suites explicites
- Substitution petit n / grand n
- Conditions réglementaires

## 7. Étape 3 : substitutions itérées
- Suites 3 à 11 termes
- Positions substituées
- Valeurs compensatoires
- Structures réglementaires

## 8. Propriétés fondamentales des puissances de deux
- Lemme général
- Exemples

---

# 🟩 PARTIE II — MÉTHODE SPECTRALE

## 9. Fondations du rapport spectral 1/2
- SA, SB (formes générales)
- Validité pour n > 0
- Définition RsP
- Preuve formelle du ratio constant 1/2
- Points de résonance (29, 31, 37, 41)
- Validation numérique (z1 à z25)

## 10. Extensions aux rapports 1/3 et 1/4
- Modèle spectral 1/3 (premier 227)
- Modèle spectral 1/4 (premier 947)
- Preuve du ratio constant 1/3
- Preuve du ratio constant 1/4

## 11. Méthode Savard — Unification générale
- Les quatre équations spectrales (positives et négatives)
- Démonstration des suites négatives
- Correspondance rang ↔ premier négatif
- Définition générale du Digamma
- Définition générale du Gap spectral

## 12. Écarts entre deux nombres premiers
- Exemple 23 / 7
- Exemple -19 / -5
- Exemple -31 / 17
- Inclusion ou non du zéro

## 13. Modèle spectral 1/3 — Écarts
- Exemple 227 / 173
- Valeurs spectrales exactes
- Validation numérique
- Équation générale d’écart
- Postulat spectral d’écart 1/3

## 14. Modèle spectral 1/4 — Écarts
- Exemple 947 / 881
- Valeurs spectrales exactes
- Équation générale d’écart
- Postulat spectral d’écart 1/4

## 15. Mentions légales
##  Résumé du fichier `methode_de_philippot.thy`

Ce fichier Isabelle/HOL constitue la base formelle de la **méthode de Philippot**, une approche structurée pour analyser la géométrie du spectre premier à travers des suites rationnelles, des équations spectrales et des rapports invariants. Il regroupe plusieurs familles de définitions, d’axiomes et de propriétés qui organisent la dynamique spectrale en trois grandes étapes.

La première partie introduit les **équations spectrales négatives**, fondées sur deux suites exponentielles (`SA_neg_eq` et `SB_neg_eq`) et une fonction dérivée (`digamma_neg_calc`). Ces objets servent à formaliser le comportement du spectre dans le régime négatif. Un axiome central établit que le **rapport spectral négatif** entre deux indices distincts est toujours égal à 1/2, ce qui constitue une propriété fondamentale de la méthode.

Le fichier développe ensuite une théorie des **asymétries spectrales**, distinguant les configurations ordonnées (structure régulière, indices croissants, relation stricte entre les listes) et chaotiques (absence d’ordre, longueurs différentes). Un lemme montre que, dans les deux cas, les indices utilisés respectent les contraintes structurelles imposées par la géométrie spectrale.

Les sections suivantes décrivent les **trois étapes de construction des suites rationnelles**.  
- **L’étape 1** présente des suites explicites de longueur 3 à 11, toutes basées sur des puissances de deux, et introduit une fonction générale permettant de générer automatiquement ces suites.  
- **L’étape 2** introduit un mécanisme de substitution : une position est modifiée et une valeur compensatoire est ajoutée pour préserver la structure spectrale. Deux régimes sont distingués (petit n et grand n), chacun avec ses règles réglementaires.  
- **L’étape 3** reprend le mécanisme de l’étape 2 mais en appliquant une division supplémentaire par 2 à chaque étape, ce qui produit une hiérarchie de suites de plus en plus fines.

Enfin, le fichier se conclut par une propriété fondamentale des puissances de deux, démontrant que le rapport entre deux termes consécutifs est toujours égal à 1/2. Cette propriété justifie la cohérence interne de toutes les étapes précédentes et renforce la structure spectrale globale.

Ce fichier constitue ainsi un socle théorique complet, combinant définitions, axiomes, suites explicites et propriétés algébriques, pour formaliser la géométrie du spectre premier selon la méthode de Philippot.
  ## 🧭 Résumé de la Méthode Spectrale

La méthode spectrale formalise une architecture complète pour analyser les rapports entre nombres premiers à partir de suites exponentielles, d’équations spectrales et de postulats inspirés de comportements numériques constants. Elle généralise la méthode de Philippot en intégrant les rapports 1/2, 1/3 et 1/4, ainsi que leurs versions négatives.

La première partie établit les formes générales des suites spectrales SA et SB, qui permettent de démontrer formellement que le rapport
(SA(n1) − SA(n2)) / (SB(n1) − SB(n2))
vaut exactement 1/2 pour tout couple d’indices naturels distincts. Cette propriété est illustrée par des exemples concrets (29, 31, 37, 41) et validée numériquement sur de larges plages d’indices.

La méthode est ensuite étendue aux rapports 1/3 et 1/4, chacun défini par ses propres équations spectrales (A_1_3, B_1_3, A_1_4, B_1_4). Les rapports spectraux constants 1/3 et 1/4 sont démontrés algébriquement pour les indices positifs, puis complétés par des axiomes pour les régimes négatifs, où aucune simplification algébrique n’est possible.

La Méthode Savard unifie ces modèles en introduisant quatre équations spectrales (positives et négatives), une définition générale du Digamma et une structure complète pour les écarts spectraux. Elle établit la correspondance entre rangs spectraux et nombres premiers, y compris dans le régime négatif.

Les sections suivantes appliquent ces outils aux écarts entre deux nombres premiers. La formule spectrale
(A_next − (B_high − D_high) − D_low) / k
reproduit exactement la quantité d’entiers entre deux premiers, pour les rapports 1/2, 1/3 et 1/4. Les exemples 23/7, −19/−5, −31/17, 227/173 et 947/881 illustrent la cohérence de cette approche.

Enfin, des postulats spectraux d’écart sont introduits pour les rapports 1/3 et 1/4, garantissant que la formule générale d’écart donne toujours la différence exacte entre deux nombres premiers. La méthode spectrale constitue ainsi un cadre unifié, cohérent et extensible pour l’étude des rapports spectraux et des écarts entre nombres premiers.
