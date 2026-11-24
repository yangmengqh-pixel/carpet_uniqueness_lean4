# Errata and deviations

These notes describe the scope of the formalization of Meng Yang,
*On the uniqueness of p-energy on the Sierpiński carpet* (arXiv:2610.26720v1).
They record differences in how Lean states or proves results used for
Theorem 2.3.

| Manuscript result | Lean formulation |
| --- | --- |
| Theorem 2.3 and the existence statement preceding it | The theorem takes the reference energy as an input satisfying Definition 2.1. The independent existence construction from reference [34, Theorem 1.1] remains outside this formalization. |
| Theorem 5.2 | The proof uses the two-function dependence result for the comparison energy. |
| Lemma 5.7, Proposition 5.8, and Theorem 8.1 | Lean proves the exceptional-set and smooth cutoff consequences needed for the weighted planar pushforwards in the low-scale argument. |
| Theorem 7.4 | Lean proves proportionality using pairwise rational relations between the density seminorms. This supplies the role of the real-quotient dimension argument. |

The [manuscript correspondence table](../README.md#correspondence-with-the-manuscript)
links the formalized arguments to their Lean files.
