# Uniqueness of self-similar p-energies on the Sierpiński carpet

The source is Meng Yang, *On the uniqueness of p-energy on the Sierpiński carpet*,
arXiv:2610.26720v1. The source PDF has SHA-256
`de9871156cc8a9059c9d94f8ba95e551ad6e002eb9331aace963e15e86e7b59a`.

**Status.** Lean proves [`CarpetEnergy.SelfSimilarPEnergy.theorem_2_3`](EnergyUniqueness.lean)
for all self-similar $p$-energies of Definition 2.1 with $1 < p < \infty$. As on p. 5,
the theorem gives $\rho=\rho^{(c)}$, $\mathcal F=\mathcal F^{(c)}$, and one positive
$c$ such that $\mathcal E(f)=c\mathcal E^{(c)}(f)$ for every $f$ in the common domain.
The proof covers both $\rho>1$ and $\rho\leq1$ and works with any Definition 2.1
energy as the reference.

## Build and verify

### Install Git and Elan

Run `git --version` to check whether Git is available. If it is missing, use the instructions for your system.

- **macOS:** Run `xcode-select --install`. [Git for macOS](https://git-scm.com/install/mac)
- **Debian or Ubuntu:** Run `sudo apt update` and then `sudo apt install git curl`. For other distributions, use your distribution's package manager. [Git for Linux](https://git-scm.com/install/linux)
- **Windows:** Install Git for Windows, then open Git Bash for the remaining commands. [Git for Windows](https://git-scm.com/install/windows)

Install Elan, the Lean toolchain manager. Run the official installer in a
terminal on macOS or Linux, or in Git Bash on Windows. [Elan installation guide](https://github.com/leanprover/elan#manual-installation)

```sh
curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh
```

Follow the installer's prompts, open a new terminal, and run `elan --version`
to confirm that Elan is available. Elan selects the Lean and Lake versions
specified by this repository when you run `lake` from the checkout.

### Build the project

Run these commands from the root of a checkout.

```sh
lake exe cache get
lake --log-level=error build
```

[lean-toolchain](lean-toolchain) selects Lean 4.37.0-rc1.
[lakefile.toml](lakefile.toml) pins Mathlib to
`31ce06eaadf4a200c0e1407c5f10953cf606b8f8`.
[lake-manifest.json](lake-manifest.json) locks the transitive dependencies.
The first command fetches precompiled Mathlib artifacts. Lake uses the
checkout's own `.lake/` directory for dependencies and build outputs.

The build passes when Lake prints `Build completed successfully`.
To build just the theorem and its dependencies, run
`lake --log-level=error build +EnergyUniqueness`. This produces
`.lake/build/lib/lean/EnergyUniqueness.olean`, which the audit imports.

### Audit Theorem 2.3

After a successful build, paste the entire block into your terminal, including
the final `LEAN` on its own line.

```sh
lake env lean --stdin <<'LEAN'
import EnergyUniqueness

#check CarpetEnergy.SelfSimilarPEnergy.theorem_2_3
#print axioms CarpetEnergy.SelfSimilarPEnergy.theorem_2_3
LEAN
```

`#check` prints the theorem's statement. The last line of a successful audit is

```text
'CarpetEnergy.SelfSimilarPEnergy.theorem_2_3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This exact axiom list confirms that the theorem and its transitive proof
dependencies are `sorry`-free and use only the three standard axioms shown.
If Lean reports `unknown module prefix 'EnergyUniqueness'`, finish the build
from the repository root and run the audit again.

## Errata and deviations

The manuscript obtains its canonical reference energy from [34, Theorem 1.1].
The Lean theorem takes the reference energy as a Definition 2.1 input.
The independent existence construction in [34] remains outside this formalization.
The proof uses the two-function case of Theorem 5.2 and derives proportionality
from pairwise rational relations, which supply the role of Theorem 7.4.
The [scope notes](docs/ERRATA-AND-DEVIATIONS.md) describe the main
differences in formulation. The table below identifies other specializations.

## Correspondence with the manuscript

| Lean file | Checked argument | Manuscript |
| --- | --- | --- |
| [Carpet.lean](Carpet.lean) | Existence and uniqueness of the nonempty compact Euclidean fixed point. Its eight similarities and their finite compositions give measurable embeddings of the carpet. | §2, pp. 3–4 |
| [CarpetCoding.lean](CarpetCoding.lean) | A continuous surjective address map satisfying the cell prefix identity, with the carpet contained in the unit square. | §2, pp. 3–4 |
| [CarpetSymmetry.lean](CarpetSymmetry.lean) | The eight square symmetries act on the carpet and carry each level's cells to cells of the same level. | §2, p. 3 |
| [CarpetMeasure.lean](CarpetMeasure.lean) | The normalized probability has full support. It is uniquely characterized by the cell masses $8^{-\lvert w\rvert}$. It scales by $1/8$ on first-level cells, gives coordinate lines zero mass, and is invariant under the square symmetries. | §2, pp. 3–4 |
| [CarpetGrid.lean](CarpetGrid.lean), [CarpetHausdorff.lean](CarpetHausdorff.lean) | The finite grid gives an upper mass bound at each scale. At dimension $\log 8/\log 3$, the Hausdorff measure is finite and positive and scales by $1/8$ on first-level cells. Normalizing it gives precisely the cell probability. | §2, pp. 3–4 |
| [PEnergy.lean](PEnergy.lean) | Definition 2.1 on real $L^p(K;m)$ for $p>1$. The graph norm is definite, and the cell and symmetry pullbacks and the continuous-function embedding are verified on $L^p$ classes. | Definition 2.1, p. 4 |
| [CylinderMeasure.lean](CylinderMeasure.lean) | Consistent finite cylinder masses determine a unique finite address measure by Kolmogorov extension. Comparison of the masses passes to a comparison of measures. | §2, p. 5 |
| [EnergyMeasure.lean](EnergyMeasure.lean) | The scaling factor of each self-similar energy is unique. The prescribed cylinder masses define its energy measure by pushforward along the address map. Its total mass is the energy, and it has the decomposition over every cell level. Energy comparison extends to measure comparison when the scaling factors agree. | §2, p. 5, Lemma 3.3(c) and the measure comparison in Lemma 7.1 |
| [EnergySeminorm.lean](EnergySeminorm.lean) | The p-th root of the energy measure of each Borel set is a seminorm bounded by the energy seminorm. | Lemma 3.3(a) |
| [EnergySymmetry.lean](EnergySymmetry.lean) | The energy measures are covariant under all eight square symmetries. | Lemma 3.3(d) |
| [EnergyContraction.lean](EnergyContraction.lean), [EnergyLipschitz.lean](EnergyLipschitz.lean) | Shifted and rescaled truncations yield the sharp bound for Lipschitz scalar composition on the full energy domain. A uniform scalar-composition estimate for the energies passes to the associated measures. | Lemma 3.3(b) |
| [EnergyLocality.lean](EnergyLocality.lean) | Level sets of continuous domain functions have zero energy measure. Two continuous domain functions whose difference is constant on a Borel set give that set the same mass. The energy measure of a shifted truncation is the restriction to its open strip. | Lemma 3.3(e)–(f) |
| [EnergyComparison.lean](EnergyComparison.lean) | One-sided energy comparison orders the scaling factors. Two-sided comparison on a common domain makes them equal. | Scaling-factor equality in Lemma 7.1 |
| [EnergyApproximation.lean](EnergyApproximation.lean), [UniformConvexApproximation.lean](UniformConvexApproximation.lean) | Uniform convexity and the continuous inclusion into the separable ambient space give a countable graph-dense continuous core and an energy-dense rational subspace. Bounded approximants with an ambient limit give a graph-domain limit in every closed convex tail and preserve graph-controlled seminorm bounds. | Dense rational subspace preceding Lemma 7.3 |
| [EnergyDominance.lean](EnergyDominance.lean) | The manuscript's weighted reference measure is finite and minimal energy-dominant for an energy-dense sequence. Its weighted Radon–Nikodym derivatives sum to one. | Before and within Lemma 7.3 |
| [RankOneSeminorm.lean](RankOneSeminorm.lean) | Comparable rational seminorms are proportional when the canonical seminorm is realized by a map into a one-dimensional real normed space. Taking p-th powers puts the multiplier in the measure comparison interval. | Proposition 7.5, p. 47 |
| [CommonDensity.lean](CommonDensity.lean) | The weighted competing densities give a common Borel density when the pointwise density ratios agree. | Proposition 7.5, pp. 47–48 |
| [EnergyDensities.lean](EnergyDensities.lean) | The roots of the Radon–Nikodym derivatives jointly define rational seminorms almost everywhere on any countable rational subspace. | Seminorm part of Lemma 7.3 |
| [EnergyWeightedSeminorm.lean](EnergyWeightedSeminorm.lean) | The root of a bounded Borel-weighted mass is a seminorm. The pointwise ratios on the dense sequence yield a bounded common density, and the weighted seminorm estimate extends the identity to the whole domain. | Equation (7.6) and the dense-domain extension in Proposition 7.5 |
| [InvariantDensity.lean](InvariantDensity.lean) | Null overlaps yield the cell restriction identity. Shared cell covariance and preimages in the energy domain give density invariance for the reference measure. The zero-one law then makes the density a.e. constant, so one positive multiplier scales every energy measure and its total mass. | Lemma 7.2 and Propositions 7.6–7.7, pp. 44 and 48–49 |
| [CarpetFolding.lean](CarpetFolding.lean), [CarpetDensity.lean](CarpetDensity.lean) | Continuous folding extends continuous domain functions from every word cell. Word maps preserve null preimages for the reference measure. Null first-level overlaps imply the cell restriction formula at every level. A common density is invariant under all word maps and square symmetries when the scaling factors agree and the overlaps are null. With the zero-one law, it gives proportionality. | Remark 6.2, Lemma 7.2 and Propositions 7.6–7.7 |
| [EnergyComponent.lean](EnergyComponent.lean) | Restricting energy measures to an invariant Borel set gives a self-similar component satisfying (Q1)–(Q5). | Lemma 6.7(b) |
| [EnergyComponentKernel.lean](EnergyComponentKernel.lean) | The component kernel is a graph-closed linear subspace containing constants. Its continuous part is an algebra and lattice, is preserved by scalar Lipschitz maps, and satisfies finite cell gluing. | Lemma 6.3 |
| [EnergyComponentDominance.lean](EnergyComponentDominance.lean) | The inverse image of an invariant set has the component masses on the address cylinders. Cylinder comparison proves that a component bounded below by a positive multiple of the energy has full measure for any minimal energy-dominant measure. | Lemma 6.8 |
| [CarpetVerticalFolding.lean](CarpetVerticalFolding.lean), [EnergyComponentProfile.lean](EnergyComponentProfile.lean) | The vertical fold maps each word cell to its bottom-row counterpart in the same column. A continuous kernel function that varies on an exterior side supplies two bottom-row plateaus, and folding and gluing give a profile equal to zero on the left and one on the right. | Lemma 6.4 |
| [CarpetConnected.lean](CarpetConnected.lean) | Corner overlaps propagate through the word cells and give connectedness. Finite unions of cells containing a point give arbitrarily small connected neighborhoods. | Geometry used in Lemma 3.7 |
| [EnergyCutoff.lean](EnergyCutoff.lean) | Restricting a nonnegative continuous domain function to a union of connected components of its positive set gives a continuous domain function of no greater energy. | Lemma 3.7 |
| [EnergyVanishing.lean](EnergyVanishing.lean) | Nonnegative uniformly bounded functions vanishing on a common set of positive measure tend to zero in Lp when their energies vanish. Nested closed convex sets in the graph norm retain the integral constraints. | Lemma 3.8 |
| [CarpetCapacity.lean](CarpetCapacity.lean) | The two opposite-side capacity infima agree and are positive, with a finite-energy competitor. Compressing a profile into the two middle-column cells multiplies its energy by $2\rho$, giving $\rho\ge 1/2$. | Lemma 3.1 |
| [AddressMeasureComparison.lean](AddressMeasureComparison.lean), [AddressStopping.lean](AddressStopping.lean), [CarpetAddressMeasure.lean](CarpetAddressMeasure.lean), [EnergyBlowup.lean](EnergyBlowup.lean) | The first-crossing cylinders are disjoint and cover the plateau almost everywhere. The coded intersection identities and the two mass budgets give a pullback satisfying the three quantitative estimates, with the energy estimate multiplied by the positive original plateau mass. | Lemma 3.5 |
| [DyadicLayerMass.lean](DyadicLayerMass.lean), [DyadicEnergyTruncation.lean](DyadicEnergyTruncation.lean) | Descending dyadic levels compare the moment and the weighted plateau masses. Disjoint open strips control the energy budget and select a truncation with positive plateau mass, comparable support mass, and the energy bound. The constants depend only on p. | Lemma 3.4 |
| [PlanarCrossing.lean](PlanarCrossing.lean), [CarpetBoundary.lean](CarpetBoundary.lean), [CarpetCrossingCapacity.lean](CarpetCrossingCapacity.lean) | The winding number of the circle forces the planar crossing property. The carpet contains the top and bottom sides of the square. The component cutoffs turn two left-to-right crossings carrying levels one and zero into a capacity competitor. | Lemma 3.10 |
| [CarpetCellCrossings.lean](CarpetCellCrossings.lean), [EnergyOppositeComponents.lean](EnergyOppositeComponents.lean) | Compact connected subsets of the open components can be chosen to meet all four corner interiors. If two side cells lack crossings, compact separation and the four-corner geometry contradict connectedness. The upper and lower components therefore share at least two crossings, which give the stated energy bound by self-similarity. | Lemma 3.9 |
| [BoundedEnergyOscillation.lean](BoundedEnergyOscillation.lean) | Bounded continuous domain functions converge to their means in Lp when their energies vanish. The proof gives a uniform bound for small energies by applying the two-component capacity estimate to thresholds on either side of the mean. | Proposition 3.6 |
| [MeasureMedian.lean](MeasureMedian.lean) | A bounded measurable real function has a median with at most half the probability in each strict tail, including when a level set has positive mass. | Equation (3.14) in the proof of Proposition 2.2 |
| [EnergySpectralGap.lean](EnergySpectralGap.lean) | Dyadic truncation and cell blowup yield a bounded function with separated plateaus. Its energy lower bound gives the spectral gap first for continuous functions after splitting around a median, and then for the whole domain by graph-norm density. | Proposition 2.2 |
| [CarpetBoundaryDensity.lean](CarpetBoundaryDensity.lean) | Word corners are dense, and each child cell touches the parent exterior. Constancy on the sides of all word profiles therefore forces constancy on the carpet. | First step of Theorem 6.6 |
| [EnergyAdjacentCells.lean](EnergyAdjacentCells.lean), [CarpetGridNeighbors.lean](CarpetGridNeighbors.lean), [EnergyGridComparison.lean](EnergyGridComparison.lean) | Folding a pair of side neighbors and applying the spectral gap controls their mean difference. Diagonal neighbors can be joined through a common side neighbor. Summation gives a uniform bound for the discrete energy of cell averages. | Lemma 6.5 and the cell estimates used in Section 4 |
| [CarpetCorners.lean](CarpetCorners.lean), [ComponentCornerInterpolation.lean](ComponentCornerInterpolation.lean), [EnergyComponentInterpolation.lean](EnergyComponentInterpolation.lean) | Symmetrized profiles interpolate nodal averages with matching traces. The discrete energy bound and uniform approximation put every continuous domain function in the kernel, and graph density gives the full kernel. | Lemma 6.5 and Theorem 6.6 |
| [EnergyQuasiUniqueness.lean](EnergyQuasiUniqueness.lean) | Opposite-side capacity and interpolation of cell averages force the same renormalization factor for any pair of energies. Applying the interpolation bounds and closed convex tail argument in both directions proves equality of the domains and two-sided energy comparison. | Energy and domain assertions in Lemma 7.1, using the interpolation argument of Section 6 |
| [EnergyPointwiseComparison.lean](EnergyPointwiseComparison.lean) | The two-sided energy comparison passes to measures. On a countable rational subspace the two density roots give comparable seminorms and satisfy the weighted normalization outside one Borel null set. The set may include any prescribed reference-null set. | Lemmas 7.1 and 7.3 |
| [EnergyFullSupport.lean](EnergyFullSupport.lean) | Uniform regularity and truncation give a continuous finite-energy cutoff. Level-set locality then puts its positive energy inside the chosen open set, so every energy-dominant measure has full support. | Section 4, p. 15 |
| [EnergyHarmonicMinimization.lean](EnergyHarmonicMinimization.lean) | The spectral gap bounds minimizing sublevels when a positive-measure set pins down the additive constant. A closed convex intersection gives an energy minimizer with fixed values on that set. | Existence of the minimizer in Lemma 4.5(a) |
| [CarpetCellBoundaries.lean](CarpetCellBoundaries.lean) | The boundaries are Borel. Nullity of the outer boundary propagates to all cell boundaries and the reference measure, and transfers to other energies. | Reductions for (4.4), Lemma 7.2, and the exceptional set in Lemma 7.3 |
| [CarpetHorizontalRows.lean](CarpetHorizontalRows.lean), [EnergyWalkScale.lean](EnergyWalkScale.lean) | Parallel rows give $\rho\leq 3^{p-1}/2$. Coordinate interpolants and the positive opposite-side capacity give $3^p/8\leq\rho$. Hence $d_h/2\lt \beta_p$ and $p\leq\beta_p$. | Geometric scale bounds used for (4.4) and Theorem 5.2 |
| [EnergyBottomStrip.lean](EnergyBottomStrip.lean), [CarpetCoordinateInterpolation.lean](CarpetCoordinateInterpolation.lean), [EnergyBoundarySeries.lean](EnergyBoundarySeries.lean), [EnergyLinearBoundaryProfile.lean](EnergyLinearBoundaryProfile.lean), [EnergySideNullity.lean](EnergySideNullity.lean), [EnergyBoundaryNullity.lean](EnergyBoundaryNullity.lean) | Scaled strip corrections converge in the graph norm, producing a profile with linear traces. Locality and the scale bound give zero energy measure on sides with affine traces. Interpolation and graph approximation give boundary nullity for all domain functions. | Equation (4.4), by a direct argument from Definition 2.1 |
| [EnergyBoundaryCovariance.lean](EnergyBoundaryCovariance.lean) | The full word-cell restriction and image formulas follow from boundary nullity. Invariant restrictions satisfy the word-cell formula and the two complementary components add to the original energy. | Lemmas 6.7 and 7.2 |
| [RankOneApproximation.lean](RankOneApproximation.lean), [EnergyProportionality.lean](EnergyProportionality.lean) | Pairwise approximate rational relations force two comparable pointwise seminorms to be proportional. Once pairwise dependence and the zero-one law are supplied for the reference energy, the comparison and covariance lemmas give a single positive multiplier on the common domain. | The final implication of Section 7 |
| [EnergyCellClamp.lean](EnergyCellClamp.lean), [EnergyBoundaryReplacement.lean](EnergyBoundaryReplacement.lean), [UniformConvexMidpoints.lean](UniformConvexMidpoints.lean), [EnergyNestedReplacement.lean](EnergyNestedReplacement.lean), [EnergyZeroTraceExtension.lean](EnergyZeroTraceExtension.lean), [EnergyPiecewiseHarmonic.lean](EnergyPiecewiseHarmonic.lean) | Clamping preserves boundary data and contracts energy. Nested variational replacements converge in the graph norm by uniform convexity. Extending zero-trace tests into a cell gives local harmonicity. The variational interior test space uses the graph closure of continuous compactly supported tests. | Lemma 4.1, with the graph-closure description of the test space |
| [CarpetWordIntegral.lean](CarpetWordIntegral.lean), [EnergyGraphPullback.lean](EnergyGraphPullback.lean), [EnergyAdjacentCellMeans.lean](EnergyAdjacentCellMeans.lean), [CarpetCellNeighborhoods.lean](CarpetCellNeighborhoods.lean), [EnergyNeighborhoodMeans.lean](EnergyNeighborhoodMeans.lean) | Cell integration gives the spectral gap on each word cell. Pullbacks are continuous in the graph norm, and the adjacent-cell mean estimate extends to all domain functions. The grid bounds the size of each neighborhood and the mean difference within it. | Equations (4.5)–(4.10) |
| [EnergyPairDependence.lean](EnergyPairDependence.lean) | The Radon–Nikodym chain rule transfers pairwise p-dependence from the sum of a pair's energy measures to any finite common dominating measure. Countability makes the transfer simultaneous for rational coefficients. | Transfer from Section 5 to Section 7 |
| [CarpetNeighborhoodMass.lean](CarpetNeighborhoodMass.lean), [CarpetGoodCells.lean](CarpetGoodCells.lean), [EnergyHarmonicSupport.lean](EnergyHarmonicSupport.lean), [EnergyNormalizedHarmonic.lean](EnergyNormalizedHarmonic.lean), [EnergyZeroOneReduction.lean](EnergyZeroOneReduction.lean) | Positive invariant mass is detected on an interior-harmonic function. Compact approximation selects interior cells with uniformly controlled neighborhood mass and arbitrarily small relative complementary mass. A graph-convergent continuous harmonic blowup then proves the zero-one law by the component kernel dichotomy. | Theorem 6.1 reduced to the specialized compactness in Proposition 4.2 |
| [EnergyMorrey.lean](EnergyMorrey.lean), [EnergyImageAreaScalar.lean](EnergyImageAreaScalar.lean), [EnergyImageArea.lean](EnergyImageArea.lean) | If $\rho>1$, finite-energy functions have continuous versions and satisfy a cell oscillation bound. The image of the carpet under a pair of these functions is Lebesgue-null, by geometric decay of the total area of cell rectangles. | The Morrey case of Theorem 5.2, image-nullity step |
| [EnergyGammaCompactness.lean](EnergyGammaCompactness.lean), [CarpetCellAverages.lean](CarpetCellAverages.lean), [CarpetCellProjections.lean](CarpetCellProjections.lean), [CarpetDiscreteEnergy.lean](CarpetDiscreteEnergy.lean), [EnergyGammaComparison.lean](EnergyGammaComparison.lean) | The normalized cell averages lift to contractive projections converging in $L^p$. The rescaled graph energies of intersecting cells have a subsequential Γ-limit, and scalar contractions pass to every such limit. Weak monotonicity, when available, compares the Γ-limit to the supremum of the discrete levels. | [34, Theorems 6.17 and 6.22] |
| [EnergyDiscreteInterpolation.lean](EnergyDiscreteInterpolation.lean), [EnergyDiscreteLimit.lean](EnergyDiscreteLimit.lean), [EnergyRenormalizationLimit.lean](EnergyRenormalizationLimit.lean), [EnergySelfSimilarization.lean](EnergySelfSimilarization.lean) | At the scale of a given Definition 2.1 energy, discrete interpolation and the cell mean estimates give equality of the finite-energy domains and two-sided bounds. Cesàro averages of cell renormalization yield a functional with the exact self-similar identity and the same comparison bounds. | [34, Theorem 6.22 and §8], construction on a given energy domain |
| [EnergyIndependenceApproximation.lean](EnergyIndependenceApproximation.lean), [EnergyCellDependence.lean](EnergyCellDependence.lean), [EnergyPositivePairDirections.lean](EnergyPositivePairDirections.lean) | Density roots converge in measure when their energy roots converge to zero. Approximation and cell covariance reduce the rank-one assertion to interior-harmonic pairs. Failure of dependence gives a simultaneous positive directional bound on a Borel set of positive pair measure. | Proposition 5.4 |
| [CarpetStoppingCells.lean](CarpetStoppingCells.lean), [CarpetRecurringGoodCells.lean](CarpetRecurringGoodCells.lean), [CarpetDirectionSelection.lean](CarpetDirectionSelection.lean) | First eligible cells are a disjoint covering away from the null boundaries. Stopping selects cells concentrating any positive-mass set inside the recurring good region. The support of the directional density map supplies a fixed profile for every finite family of directions. | Theorem 5.5, cell selection |
| [EnergyNormalizedPair.lean](EnergyNormalizedPair.lean), [EnergyNormalizedPairMeasure.lean](EnergyNormalizedPairMeasure.lean), [EnergyDirectionalMeasureEstimates.lean](EnergyDirectionalMeasureEstimates.lean), [EnergyPairDensityBounds.lean](EnergyPairDensityBounds.lean), [EnergyFixedDirections.lean](EnergyFixedDirections.lean), [EnergyFixedRealDirections.lean](EnergyFixedRealDirections.lean) | The specialized harmonic compactness yields a continuous harmonic pair with unit total energy whose directional energy measures are fixed multiples of the pair measure. The identities hold for all real coefficients, with coercive directional bounds. | Theorem 5.5, conditional on harmonic compactness |
| [EnergyFoldingAmplification.lean](EnergyFoldingAmplification.lean), [EnergyRootUniformConvex.lean](EnergyRootUniformConvex.lean), [EnergyNormingMatrix.lean](EnergyNormingMatrix.lean) | Folding preserves the ambient $L^p$ norm and amplifies energy. The rescaled folds transfer the graph norm's uniform midpoint deficit to the energy root. For an independent pair of unit profiles, the matrix of two norming functionals has nonzero determinant. | Proposition 5.6, determinant argument |
| [EnergyRelativeGeneralizedContraction.lean](EnergyRelativeGeneralizedContraction.lean), [CarpetGammaHomogeneity.lean](CarpetGammaHomogeneity.lean) | Every rescaled graph Γ-limit has scalar homogeneity and constant invariance. Finite mixed-norm contraction passes through joint Γ-recovery, cell renormalization, and the averaging limit, including the maximum-norm endpoint. | [34, §8] and [27, Definition 2.2], on a given energy domain |
| [EnergyLocalMidpointDeficit.lean](EnergyLocalMidpointDeficit.lean), [ScalarPowerIncrement.lean](ScalarPowerIncrement.lean) | The energy-root midpoint deficit holds on every cylinder and hence as a measure inequality. A scalar power increment is bounded by its right-endpoint derivative times the increment. | Proposition 4.2, local energy estimates |
| [EnergyFirstVariation.lean](EnergyFirstVariation.lean), [PlanarDistributionRows.lean](PlanarDistributionRows.lean), [HarmonicMorreyObstruction.lean](HarmonicMorreyObstruction.lean) | A matrix whose rows are linear first variations of two energy-independent profiles is invertible. Two independent bounded distributional derivative rows force a finite planar measure to be absolutely continuous. In the Morrey regime with $\rho>1$, an interior-weighted pair pushforward cannot have bounded distributional gradient. | Proposition 5.6 and the Morrey case of Theorem 5.2 |
| [SobolevWeightTruncation.lean](SobolevWeightTruncation.lean) | The scalar truncations have the bounds and derivative formulas used to control the reciprocal powers of the planar weight. | Equations (8.4)–(8.7) |
| [EnergyClippedHarmonic.lean](EnergyClippedHarmonic.lean), [EnergyLocalHarmonicCauchy.lean](EnergyLocalHarmonicCauchy.lean), [EnergyLocalHarmonicLimit.lean](EnergyLocalHarmonicLimit.lean) | The clipped variation gives a local energy estimate. Uniformly Cauchy harmonic profiles of bounded energy have graph-convergent pullbacks to an interior cell, with a continuous limit. | Proposition 4.2, clipped comparison and graph convergence |
| [CarpetNeighborhoodShape.lean](CarpetNeighborhoodShape.lean), [CarpetNeighborhoodRescaling.lean](CarpetNeighborhoodRescaling.lean), [EnergyNeighborhoodPasting.lean](EnergyNeighborhoodPasting.lean), [EnergyNeighborhoodVariation.lean](EnergyNeighborhoodVariation.lean) | Finite grid offsets give a subsequence with a common shape. The affine identifications preserve corresponding cell parameters and smaller neighborhoods. Pasting with a cutoff preserves harmonicity on the open first neighborhood. | Proposition 4.2, shape selection and pasting |
| [EnergyMorreyCompactness.lean](EnergyMorreyCompactness.lean), [EnergyMorreyHarmonicBlowup.lean](EnergyMorreyHarmonicBlowup.lean) | If $\rho>1$, Morrey oscillation bounds and Arzelà–Ascoli give uniform subsequences. The neighborhood energy ratio controls the normalized paste, so the central pullbacks converge in the graph norm. This proves the zero-one law for all Definition 2.1 energies in this regime. | Proposition 4.2 and Theorem 6.1 when $\rho>1$ |
| [EnergyRelativeSelfSimilarEnergy.lean](EnergyRelativeSelfSimilarEnergy.lean) | Given a Definition 2.1 energy, the discrete construction yields another Definition 2.1 energy on the same domain and scale with generalized contraction and linear first variations. Finite graph symmetry, the scalar power midpoint inequality, and uniformly small symmetric increments pass to the Γ-limit and the renormalization means. | [34, §8] and [27, §3], construction on a given energy domain |
| [EnergyVariationCells.lean](EnergyVariationCells.lean), [EnergyStationaryVariation.lean](EnergyStationaryVariation.lean), [EnergyVariationAffineLimit.lean](EnergyVariationAffineLimit.lean) | Linear first variations satisfy Hölder bounds and decompose over cells. Uniform affine approximation and Hölder show that the cell sums give the first variation of a smooth composition. Stationary directional densities prescribe the cell first variations. | Section 4, equation (4.3) on the continuous core, and Proposition 5.6 |
| [EnergyWeightedPlanarRows.lean](EnergyWeightedPlanarRows.lean), [EnergyPlanarPowerWeight.lean](EnergyPlanarPowerWeight.lean), [EnergyMorreyRankOne.lean](EnergyMorreyRankOne.lean) | For a stationary harmonic pair, the planar derivative rows are bounded by the conjugate-exponent norm of the test against the cutoff-weighted pushforward. The row matrix is invertible. In the Morrey regime, absolute continuity contradicts the null image, giving the rank-one assertion for the smooth comparison energy. | Proposition 5.6 and the Morrey case of Theorem 5.2 |
| [EnergyMorreyUniqueness.lean](EnergyMorreyUniqueness.lean) | If $\rho>1$, any pair of Definition 2.1 energies have the same scale and domain and one positive constant scales the energy on the whole domain. | Theorem 2.3 in the Morrey regime |
| [EnergyNeighborhoodPoincare.lean](EnergyNeighborhoodPoincare.lean) | The integral of the centered profile on a cell neighborhood is bounded by the sum of its pullback energies, with a constant uniform in scale and location. | Lemma 4.3, inequality (4.11) |
| [EnergySmoothCompositionBound.lean](EnergySmoothCompositionBound.lean) | Smooth composition of continuous profiles satisfies the energy bound in terms of the derivative coefficients integrated against their energy measures. | Proposition 5.11, inequality (5.37) |
| [EnergyNeighborhoodZeroPoincare.lean](EnergyNeighborhoodZeroPoincare.lean) | A function with zero exterior values satisfies the neighborhood Poincaré bound with no centering term. | Lemma 4.4 |
| [EnergyHarmonicReplacement.lean](EnergyHarmonicReplacement.lean), [EnergyCellHarmonicReplacement.lean](EnergyCellHarmonicReplacement.lean) | Prescribing values almost everywhere on the union of exterior cells determines a unique minimizer of both the global energy and the sum on the selected cells. | Lemma 4.5(a), with the almost-everywhere exterior condition |
| [EnergyHarmonicComparison.lean](EnergyHarmonicComparison.lean) | Generalized contraction gives the lattice inequality and comparison of harmonic replacements with ordered exterior data. | Lemma 4.6, with the almost-everywhere exterior condition |
| [EnergyNeighborhoodHarnackEstimate.lean](EnergyNeighborhoodHarnackEstimate.lean) | Given the neighborhood Harnack bound, the nonnegative harmonic replacements of the two signs yield an essential supremum estimate for a centered harmonic profile. | Proposition 4.8, conditional on Lemma 4.7 |
| [EnergySupportedApproximation.lean](EnergySupportedApproximation.lean), [EnergyInteriorHarmonicExterior.lean](EnergyInteriorHarmonicExterior.lean) | A domain function vanishing off a closed interior region is approximable in the graph norm by continuous interior variations. Thus interior-harmonic functions minimize against the measurable exterior value constraint for such regions. | Interior test spaces in Lemmas 4.5 and 4.7 |
| [EnergyNeighborhoodOscillation.lean](EnergyNeighborhoodOscillation.lean), [CarpetNeighborhoodBuffers.lean](CarpetNeighborhoodBuffers.lean) | Harnack contracts essential oscillation between the two cell neighborhoods. Metric buffer estimates locate sufficiently fine neighborhoods inside the open part of a larger neighborhood. | Oscillation step for Proposition 4.9, conditional on Lemma 4.7 |
| [EnergyStationaryPlanarDensity.lean](EnergyStationaryPlanarDensity.lean) | For an independent continuous stationary harmonic pair, the weighted planar pushforward has a Lebesgue density with integrable first weak derivatives. Each derivative is the density times a coefficient in the weighted $L^p$ space. | Proposition 5.6, weighted weak derivative step |
| [EnergyStationaryPlanarSobolev.lean](EnergyStationaryPlanarSobolev.lean) | The $p$-th root of the weighted pushforward density belongs to $W^{1,p}(\mathbb R^2)$. Smooth regularization, the weak chain rule, and dominated convergence identify its derivatives. | Proposition 5.6 for continuous stationary profiles and continuous interior cutoffs |
| [EnergyWeightedCapacityNonconcentration.lean](EnergyWeightedCapacityNonconcentration.lean), [EnergyPairCellPushforward.lean](EnergyPairCellPushforward.lean) | Small weighted cutoffs keep the volume pushforward from concentrating on the exceptional set. A cutoff equal to one on an interior cell gives a weighted pushforward that dominates the scaled cell pushforward. | Proposition 5.11 conditional on the smooth weighted cutoffs, and the cell restriction in Theorem 5.2 |
| [EnergyHarmonicNeighborhoodVersion.lean](EnergyHarmonicNeighborhoodVersion.lean), [EnergyHarnackHarmonicBlowup.lean](EnergyHarnackHarmonicBlowup.lean) | Neighborhood Harnack gives continuous local harmonic versions with a uniform modulus. After normalization and pasting, uniform compactness upgrades to graph compactness on the central cell. | Propositions 4.9 and 4.2 conditional on Lemma 4.7 |
| [EnergyCarpetSobolev.lean](EnergyCarpetSobolev.lean), [EnergyPlanarSobolevExponent.lean](EnergyPlanarSobolevExponent.lean) | The cell mean increments give a geometric series of $L^q$ bounds on the continuous core. When $\rho\leq1$, the strict Sobolev range contains an exponent with $2p/q<2-p$. | Strict-range version of (5.38) sufficient for the continuous tests in the planar argument |
| [EnergyPlanarDensityObstruction.lean](EnergyPlanarDensityObstruction.lean) | Smooth ball pulses at a point satisfying the three density bounds contradict the carpet Sobolev inequality. A local upper bound of order $r^{2-p}$ for the volume pushforward suffices. | Theorem 5.2, Case 2, inequalities (5.39)–(5.41) and the exponent contradiction |
| [PlanarLowerDensity.lean](PlanarLowerDensity.lean), [PlanarDensityCutoffs.lean](PlanarDensityCutoffs.lean) | Differentiation gives a lower quadratic density at almost every point of each finite planar measure. A Vitali cover and finite smooth cutoff construction give small unweighted cutoffs on compact subsets where the upper growth of order $r^{2-p}$ is unbounded. | Lemma 5.9 and the consequence of Lemma 5.10 needed for the weaker upper bound |
| [EnergyStationaryCellDensity.lean](EnergyStationaryCellDensity.lean), [EnergyLowScaleRankOne.lean](EnergyLowScaleRankOne.lean) | Harmonic compactness gives the independent stationary pair and a positive-energy interior cell with a Sobolev dominator. Weighted exceptional-set cutoffs then give the required density point and force pairwise energy dependence. | Theorem 5.2, Case 2, conditional on harmonic compactness and the weighted cutoffs |
| [EnergyLowScaleUniqueness.lean](EnergyLowScaleUniqueness.lean) | The constructed comparison energy satisfies neighborhood Harnack. The weighted exceptional-set cutoffs then imply equality of scale and domain and proportionality for any pair of Definition 2.1 energies at $\rho\leq 1$. | Theorem 2.3, conditional on the weighted cutoffs in the low-scale case |
| [CarpetVolumeGrowth.lean](CarpetVolumeGrowth.lean), [EnergyBallPoincare.lean](EnergyBallPoincare.lean), [EnergyBallCapacityUpper.lean](EnergyBallCapacityUpper.lean) | Normalized Hausdorff measure has two-sided power volume bounds at radii up to one. Cell Poincaré and a cutoff transported between equal-shape neighborhoods give the ball Poincaré and upper capacity bounds at the walk dimension. | Inputs to the Harnack result used in Lemma 4.7, [37, Corollary 2.8] |
| [EnergyDistanceSpanningSeparation.lean](EnergyDistanceSpanningSeparation.lean), [EnergyLogSeparation.lean](EnergyLogSeparation.lean) | Ball Poincaré and a disjoint ball selection give a lower energy bound for separating two sets that meet every distance in a fixed annulus. | Carpet specialization of [37, Lemma 5.10] |
| [EnergyApproximateLevelCrossing.lean](EnergyApproximateLevelCrossing.lean), [EnergyApproximateLogBound.lean](EnergyApproximateLogBound.lean), [EnergyBallHarnack.lean](EnergyBallHarnack.lean) | Graph approximants have crossing level sets and controlled shifted log energy. The lower separation bound yields the almost-everywhere Harnack comparison on balls. | Ball estimate for Lemma 4.7, adapting the argument of [37, Proposition 5.11] |
| [EnergyCellNeighborhoodHarnack.lean](EnergyCellNeighborhoodHarnack.lean) | A uniformly finite, connected cover by balls propagates the comparison across the cell neighborhood. Taking the positive part preserves the minimizing property on cells where the profile is already nonnegative. | Lemma 4.7 at $\rho\leq1$ for the constructed comparison energy |
| [PlanarTranslationAveraging.lean](PlanarTranslationAveraging.lean), [PlanarWeightedMollifier.lean](PlanarWeightedMollifier.lean), [PlanarWeightedCutoffTransfer.lean](PlanarWeightedCutoffTransfer.lean) | The weak translation estimate controls mollification against the signed derivative kernel. Reciprocal cutoffs transfer small unweighted test budgets to small weighted ones for a compactly supported planar measure dominated by a Sobolev root density. | Proposition 5.8 and Section 8, in the smooth cutoff form used by Proposition 5.11 |
| [PlanarMaximalSobolevCutoffs.lean](PlanarMaximalSobolevCutoffs.lean), [PlanarWeakBallPoincare.lean](PlanarWeakBallPoincare.lean), [PlanarQuadraticDensity.lean](PlanarQuadraticDensity.lean) | The maximal estimate, the weak ball Poincaré inequality and the gradient growth estimate give small unweighted cutoffs for the exceptional set with unbounded upper quadratic density. | Lemma 5.7, in the form used for the Sobolev-dominated energy pushforward |
| [PlanarExceptionalCutoffs.lean](PlanarExceptionalCutoffs.lean), [EnergyLowScaleRankOneProof.lean](EnergyLowScaleRankOneProof.lean) | Weighted small cutoffs and nonconcentration leave positive volume mass outside the exceptional set. The density point and the Sobolev contradiction yield pairwise energy dependence. | Proposition 5.11 and Theorem 5.2, Case 2 |
| [EnergyUniqueness.lean](EnergyUniqueness.lean) | The two scaling regimes give equality of renormalization factors, equality of domains, and proportionality for every pair of Definition 2.1 energies. | Theorem 2.3 |

## License

The original Lean proof code is licensed under
[Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).
See [LICENSE](LICENSE) for the license notice.

## Attribution

The Lean formalization workflow was based on the `lean-workflow` skill from
Scott Armstrong’s [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills).
The original skill materials are licensed under
[Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).
