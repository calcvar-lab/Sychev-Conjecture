# Sychev's conjecture and Tonelli's partial regularity for one-dimensional obstacle problems

Prépublication (2026) d’Omar Anza Hafsa, Adel Hachache et Jean-Philippe Mandallena, tous affiliés à Nîmes Université, Laboratoire MIPA.

Le projet réunit l’article, une formalisation de ses principaux résultats en Lean 4 et un Visual Paper interactif. L’article étudie la régularité partielle de Tonelli pour les solutions de problèmes variationnels unidimensionnels à deux obstacles.

## Article et références

- [PDF de référence](paper/article.pdf) et [variante jointe à la formalisation](paper/variants/Tonelli-obstacles-lean.pdf).
- La bibliographie de l’article figure à la fin du PDF et dans la [source TeX](website/source/src.tex). Elle comprend notamment Tonelli (1923), Sychev (1989, 1991, 1992 et 2011) et Gratwick, Sychev et Tkachov (2016).
- Le [fichier BibTeX du modèle LeanProject](paper/bibliography/LeanProject.bib) crédite le modèle d’origine. La [citation du projet et de l’article](CITATION.cff) est disponible au format CFF.

## Formalisation Lean

Le [guide de la formalisation](lean/README.md) relie les résultats du papier aux déclarations Lean. `TonelliObstacle.main_theorem` formalise le théorème 2.2. Les corollaires 2.3 et 2.4 sont représentés notamment par `TonelliObstacle.sychev_conjecture` et `TonelliObstacle.C1_near_contact`. Les autres énoncés, exemples et explications de l’article ou du Visual Paper sont à distinguer des déclarations répertoriées dans ce guide.

La compilation sous Lean 4.33.1 a réussi. Pour les trois déclarations principales, `#print axioms` a confirmé les dépendances `propext`, `Classical.choice` et `Quot.sound`. Le module [`Project.Remarks`](lean/Project/Remarks.lean) formalise les remarques complémentaires de l’article.

Installer Elan et disposer d’un accès réseau pour télécharger Lean 4.33.1 et Mathlib à la révision du manifeste. Depuis la racine du dépôt, exécuter les commandes suivantes.

```sh
cd lean
lake exe cache get
lake build
```

## Visual Paper

Depuis la racine du dépôt, lancer un serveur statique avec Python 3.

```sh
python -m http.server 8000 --bind 127.0.0.1
```

Ouvrir [le Visual Paper local](http://127.0.0.1:8000/website/). La page utilise MathJax et Google Fonts via leurs CDN. Le [guide des sources](website/source/README.md) décrit les fichiers livrés.

Pour une future publication GitHub Pages, préparer un répertoire statique contenant `website/index.html` et `paper/article.pdf` à ces emplacements relatifs. Le point d’entrée serait `/Sychev-Conjecture/website/`, et le lien PDF serait résolu sous `/Sychev-Conjecture/paper/`.

## Organisation

| Chemin | Contenu |
| --- | --- |
| `lean/` | Racine Lake, modules Lean et correspondance avec l’article |
| `paper/` | PDF, variante et référence du modèle LeanProject |
| `website/` | Page statique générée et sources, dont le manuscrit TeX et les figures |
| `scripts/` | Mise à jour coordonnée des versions Lean et Mathlib |
| `docs/` | Rapport de migration et configuration du modèle d’origine |
| `.github/` | CI Lean, modèles de tickets et configuration Dependabot |
| `.devcontainer/` et `.vscode/` | Environnement de développement et recommandation Lean pour VS Code |

## Licence

Le [texte Apache 2.0](LICENSE) provient du projet Lean d’origine. La diffusion de l’article, de ses figures et des ressources du Visual Paper a été autorisée pour ce dépôt et son site.
