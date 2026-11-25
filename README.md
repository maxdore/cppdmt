# Discrete Morse Theory in Cubical Agda

This artefact accompanies the paper

> **Studying the Topology of Images with Discrete Morse Theory in Cubical Agda**
> Maximilian Doré. Certified Proofs and Programs 2027.

It formalises discrete Morse theory for graphs and for 2-full two-dimensional
cubical complexes in Cubical Agda. The main results are Morse theorems, which
say that the realisation of a complex is equal to the realisation of its Morse
reduct, making crucial use of univalence. The theory is then applied to
black-and-white images: the artefact computes a Morse matching for any bitmap
and works out the homotopy type of two concrete images, a portrait (two points)
and a mug (a bouquet of two circles).

You can browse the code with clickable cross-references online at
<https://maxdore.github.io/cppdmt/>
or in `docs/index.html` in this folder.

---

## 1. Installation and typechecking

### Requirements

The development has been typechecked with both of the following setups:

| Agda        | `cubical` library |
|-------------|-------------------|
| **2.8.0**   | **v0.9**          |
| 2.6.4.3     | v0.7              |

All modules use the `--guardedness` flag. cubical v0.9 is compiled with it;
under cubical v0.7 the flag does nothing. Also under v0.7, Agda warns that
`BinaryRelation` doesn't export `isTotal` (`Prelude.agda`, line 50); this
warning is harmless.

### Installing Agda

Agda 2.8.0 is available as a prebuilt binary for Linux, macOS and Windows from
the [GitHub release page](https://github.com/agda/agda/releases/tag/v2.8.0).
Alternatively, it can be built with cabal:

```sh
cabal update
cabal install Agda-2.8.0
agda --version             # should print: Agda version 2.8.0
```

See the [Agda installation guide](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html)
for further options, e.g. package managers.

### Installing the cubical library

```sh
git clone https://github.com/agda/cubical.git
cd cubical
git checkout v0.9
```

Then register it with Agda by adding the absolute path of its `.agda-lib` file
to `~/.agda/libraries` (create the file if it doesn't exist):

```sh
mkdir -p ~/.agda
echo "$PWD/cubical.agda-lib" >> ~/.agda/libraries
```

The library declares itself as `cubical-0.9`.

### Type-checking

All module names are relative to this folder, so run Agda from here:

```sh
agda -l cubical-0.9 -i . Everything.agda
```

`Everything.agda` imports every module of the development. Every module is
checked with `--safe`, so a successful run means that there are no postulates
and no unsafe pragmas anywhere.

The HTML rendering in `docs/` was generated with Agda 2.8.0 and cubical v0.9
by

```sh
agda -l cubical-0.9 -i . --html --html-dir=docs Everything.agda
```

**Running time.** Almost all of the time goes into the two image examples,
`Examples/Voevodsky.agda` and `Examples/Mug.agda`; each is a long table of
`refl`s over a large bitmap. It takes about 10 minutes on an M1 MacBook.

## 2. Overview of the development

### Structure

The development has three layers. Each comes in a 1-dimensional (graph) and a
2-dimensional (complex) version, and the 2-dimensional version is built to
*reduce to* the 1-dimensional one, not to repeat it.

```
             1-dimensional               2-dimensional
             ─────────────               ─────────────
realisation  CType1          ◀─noSq──    CType2
                │                           │
matchings    GraphMatching   ◀───────    ComplexMatching
                │                           │
Morse thm    GraphMorse      ◀───────    ComplexMorse ◀── ImageComplex
                                                             │
reading off  GraphForest, GraphBouquet  ◀─────────────── ImageMatching
the result                                                   │
                                                          ImageMorse
                                                             │
                                                 Examples.Voevodsky, Examples.Mug
```


### Modules

| Module | Lines | Paper | Contents |
|---|---:|---|---|
| `CType1` | 143 | §3.1 | `CType¹`, its realisation `∣_∣`, examples (circle, wedge of circles) |
| `CType2` | 60 | §5.1 | `CType²`, its realisation `∣_∣`, `noSq` |
| `GraphForest` | 39 | §3.2 | `ForestCollapse`: a forest is its set of roots |
| `GraphBouquet` | 90 | §3.2 | `CycleCollapse`: a graph with a spanning tree is a bouquet of circles |
| `GraphMatching` | 191 | §4.1–4.2 | `Graph`, `Crit₀`, `Crit₁`, gradient paths `_⇝_`, `Matching`, `sink`, `sinkUniq` |
| `GraphMorse` | 183 | §4.2–4.3 | `ϕ`, `ι`, `⇝Contr`, `rinv`, `linv`, `MorseTheorem` |
| `ComplexMatching` | 157 | §5.2 | `Complex`, `MatchingData`, `_⇝₁_`, `acyclic₁`, `2FullMatching` |
| `ComplexMorse` | 379 | §5.3 | `SquareCollapse`, Morse reduct, `MorseTheorem` |
| `ImageComplex` | 303 | §6 | The complex of a bitmap |
| `ImageMatching` | 666 | §6 | The matching `Match` and the proof that it is a 2-full matching |
| `ImageMorse` | 194 | §6 | Tools for reading off the Morse reduct of a concrete bitmap |
| `Examples/Line` | 80 | Ex. 3.3 | The infinite line is contractible |
| `Examples/Two` | 137 | Ex. 3.4 | Two vertices and two edges form a circle; its cohomology |
| `Examples/Trees` | 219 | §3.2 | `ForestCollapse` on a finite forest, the ray and the binary tree |
| `Examples/Bouquets` | 93 | §3.2 | `CycleCollapse` on three small graphs |
| `Examples/3DCube` | 462 | Ex. 5.3 | The surface of the cube is a sphere |
| `Examples/Book` | 434 | Ex. 5.6, 5.10 | The infinite book, its matching, and `bookIsUnit` |
| `Examples/SquareCollapse` | 465 | Ex. 5.13 | `SquareCollapse` on a strip of two squares |
| `Examples/Corner` | 77 | Ex. 6.2 | Two pixels touching at a corner are connected |
| `Examples/ImageMatching` | 542 | §6 | The image matching on small bitmaps |
| `Examples/Voevodsky` | 1184 | Ex. 6.5 | The 64×64 portrait has the homotopy type of `Bool` |
| `Examples/Mug` | 425 | Ex. 6.6 | The 29×22 mug is a bouquet of two circles |


### Where to find the results of the paper

Each statement in the paper also has an Agda logo that links to the code online.

| Paper | Agda |
|---|---|
| Def. 3.1 (`CType¹`) | `CType1.CType¹` |
| Def. 3.2 (realisation) | `CType1.∣_∣` |
| Ex. 3.3 (the line) | `Examples.Line.∣line₁∣≡⊤`, `line-isContr` |
| Ex. 3.4 (two edges) | `Examples.Two.∣two₁∣≡S¹` |
| Lemma 3.5 (forests) | `GraphForest.ForestCollapse` |
| Lemma 3.6 (bouquets) | `GraphBouquet.CycleCollapse` |
| Def. 4.1 (graph) | `GraphMatching.Graph` |
| Def. 4.2 (`Crit₀`, `⇒ᶜ`) | `GraphMatching.Paths` |
| Def. 4.3 (gradient paths) | `GraphMatching.Paths._⇝_` |
| Lemma 4.4 | `GraphMatching.Matching.⇝IsHProp` |
| Def. 4.5 (Morse matching) | `GraphMatching.Matching`, `acyclic` |
| Def. 4.6 (Morse reduct) | `GraphMatching.Paths.Crit₁` |
| Def. 4.7 (sink) | `GraphMatching.Matching.sink` |
| Lemma 4.8 | `GraphMatching.Matching.sinkUniq` |
| Def. 4.9 (`ϕ`) | `GraphMorse.Morse.ϕ` |
| Def. 4.10 (`ι`) | `GraphMorse.Morse.ι` |
| Lemma 4.11 | `GraphMorse.Morse.⇝Contr` |
| Lemma 4.12 | `GraphMorse.Morse.rinv` |
| Lemma 4.13 | `GraphMorse.Morse.linv` |
| **Theorem 4.14** (Morse theorem for graphs) | **`GraphMorse.Morse.MorseTheorem`** |
| Def. 5.1 (`CType²`) | `CType2.CType²` |
| Def. 5.2 (realisation) | `CType2.∣_∣` |
| Ex. 5.3 (cube) | `Examples.3DCube` |
| Lemma 5.4 | `CType2.noSq` |
| Def. 5.5 (complex) | `ComplexMatching.Complex` |
| Ex. 5.6 (infinite book) | `Examples.Book.complex` |
| Def. 5.7 (`⇒₁`) | `ComplexMatching.GradientPaths._⇒₁_` |
| Def. 5.8 (`⇝₁`) | `ComplexMatching.GradientPaths._⇝₁_` |
| Def. 5.9 (2-full matching) | `ComplexMatching.2FullMatching` |
| Ex. 5.10 (book matching) | `Examples.Book.matching`, `bookIsUnit` |
| Def. 5.11 (square-collapsed graph) | `ComplexMorse.MorseSquares.E⁻` |
| Lemma 5.12 | `ComplexMorse.MorseSquares.SquareCollapse` |
| Ex. 5.13 (strip) | `Examples.SquareCollapse` |
| Def. 5.14 (Morse reduct) | `ComplexMorse.MorseSquares` (`Crit₀`, `P⁻.Crit₁`) |
| **Theorem 5.15** (Morse theorem for 2-full complexes) | **`ComplexMorse.Morse.MorseTheorem`** |
| Def. 6.1 (image complex) | `ImageComplex.Image` (`V`, `E`, `Sq`, `complex`) |
| Ex. 6.2 (corner) | `Examples.Corner.isContr∣corner∣` |
| Def. 6.3 (image matching) | `ImageMatching.Match` |
| Lemma 6.4 | `ImageMatching.Match.matching` |
| **Ex. 6.5** (portrait) | **`Examples.Voevodsky.∣voevodsky∣≡Bool`** |
| **Ex. 6.6** (mug) | **`Examples.Mug.∣mug∣≡BouquetBool`** |


## 3. Use of AI

As explained in the paper (§1, "Artefact and Disclosure of AI Use"), parts of
this development were written with Anthropic's Fable. In particular, the
following statements were devised with the help of Fable, since these are quite
short (one only has to consult the definition of realisation), one can readily
check that these are meaningful:

```agda
ComplexMorse.Morse.MorseTheorem : ∣ V , E , Sq ∣ ≡ GR.∣ Crit₀ , P⁻.Crit₁ ∣
Examples.Voevodsky.∣voevodsky∣≡Bool : ∣ V , E , Sq ∣ ≡ Bool
Examples.Mug.∣mug∣≡BouquetBool       : ∣ V , E , Sq ∣ ≡ Bouquet Bool
```


