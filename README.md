# A Normalizing Computation Rule for Propositional Extensionality in Higher-Order Minimal Logic

This is an Agda formalization of the results in the paper A Normalizing Computation Rule for Propositional Extensionality in Higher-Order Minimal Logic,
submitted to the Post-Proceedings of the TYPES 2016 conference.

*Note* This formalization was built using Agda version 2.5.2 and the Agda standard library version 0.13.  It has not been tested with other versions of Agda.

The following is a guide to which lemmas in the paper correspond to which terms in the Agda formalisation


| Lemma | File | Term |
|---|---|---|
| Lemma 3.1 | PHOML / PathSub / PS.agda | pathSub-•PS |
| Lemma 3.2 | PHOML / PathSub / SP.agda | pathSub-•SP |
| Lemma 7 (Confluence) | PHOML / Red / Diamond.agda | diamond |
| Lemma 8 (Reduction respects path substitution) | PHOML / Red / Base.agda | ⇒-resp-ps |
| Lemma 10 (Context Validity) | PHOML / Meta / ConVal.agda | context-validity |
| Lemma 11 (Weakening) | PHOML / Meta / ConVal.agda | weakening |
| Lemma 12.1 (Type Validity) | PHOML / Meta / TypeVal.agda | prop-validity |
| Lemma 12.2 (Type Validity) | PHOML / Meta / TypeVal.agda | eq-validity₁ |
| | | eq-validity₂ |
| Lemma 13.1 (Generation) | 
| Lemma 17 (Subject Reduction) | PHOML / Meta.agda | Subject-Reduction-R |
| Lemma 19 (Well-Typed Substitution) | PHOML / Meta.agda | substitution |
| Lemma 24 (Conversion) | PHOML / Compute.agda | conversionP, conversionE |
| Lemma 25 (Expansion) | PHOML / Compute.agda | expansionT, expansionP, expansionE |
| Lemma 26 (Reduction) | PHOML / Compute.agda | reductionT, reductionP, reductionE |
| Lemma 28 | PHOML / Compute.agda | ⊧c |
| Lemma 30 | PHOML / Compute.agda | Lemma30 |
| Lemma 31 | PHOML / Compute.agda | ⊧ref |
| Lemma 32 | PHOML / Compute.agda | ⊧canon, ⊧canon' |
| Lemma 33 | PHOML / Compute.agda | ⊧neutralP |