# Formalization of a PAC Checker #

[This directory](https://bitbucket.org/isafol/isafol/src/master/PAC_Checker/)
used to contain Pastèque, a PAC checker verified in Isabelle, but it has now moved
to the [Archive of Formal Proofs](https://www.isa-afp.org/entries/PAC_Checker.html). The formalisation is
described in an [FMCAD
paper](http://fmv.jku.at/papers/KaufmannFleuryBiere-FMCAD20.pdf).



## Authors ##

* [Mathias Fleuy](mailto:mathias.fleury shtrudel jku.at)
* [Daniela Kaufmann](http://fmv.jku.at/kaufmann/)

## TODOs ##
Will Pastèque need subtraction?
* Subtraction can't be implemented non-destructively (yet?)
  -> Just reimplement the Addition with flipped cases
The following Theories do not work yet with Isabelle_LLVM
* PAC_Map_Rel.thy
  * Line 237 - `hm.assn` is not defined in Isabelle_LLVM - Maybe Hashmaps are not available in 
    Isabelle-LLVM?
* `PAC_Checker_Relation.thy`
  * Line 19 - class `hashable` is not known in Isabelle_LLVM import?
