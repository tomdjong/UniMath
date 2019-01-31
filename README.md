Univalent Mathematics
=====================

This is the [Coq](https://coq.inria.fr/) formalisation of the constructive Scott model of PCF.
It uses the [UniMath](https://github.com/UniMath/UniMath) library.
It includes a copy of the UniMath library for compatibility and to make it easy to run without too much setting up.

Installation
------------

For general instructions, see 
[INSTALL.md](https://github.com/tomdjong/UniMath/blob/paper/INSTALL.md).

Use 
```bash
$ make Partiality
```
in the root directory to make the PCF formalisation

Use
```bash
$ make doc
```
in the root directory to create HTML documentation that allow for easy reading
of the code. Find the documentation at enhanced-html/index.html.

File listing
------------

- UniMath/Partiality/PartialElements.v

  General theory of partial elements, i.e. the lift of a type and the lift of a
  set as a dcpo with bottom 
- UniMath/Partiality/LiftMonad.v

  The monad structure on the lift and the Kleisli extension as a dcpo morphism
- UniMath/Partiality/PCF.v

  The results on PCF: most importantly Soundness and Adequacy

**Auxiliary files**
- UniMath/MoreFoundations/ClosureOfHrel.v

  Reflexive transitive closure of a (propositional valued) relation
- UniMath/MoreFoundations/PropExt.v

  Some consequences of Propositional Extensionality
- UniMath/MoreFoundations/WeaklyContant.v

  Some results on weakly constant functions from "Notions of Anonymous
  Existence in Martin-Löf Type Theory" by Kraus et al.


