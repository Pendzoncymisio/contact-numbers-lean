# Certificate generators

These scripts produced the machine-generated Lean files in `ContactNumbers/`
(the certificate list for n = 7, the serialized search trees for n = 8 and n = 9,
and the pattern-obstruction certificates).

**They are not part of the trust base.** Their output is *data*: lists of natural
numbers embedded in Lean source. Nothing about the correctness of these scripts is
assumed anywhere. What makes the data sound is that the Lean kernel checks, for every
leaf of every tree, that the certificate it carries actually discharges that case
(`walk`, `killcheck`, `checkCert` and their soundness lemmas). A bug in a generator
can only produce a certificate the kernel rejects, never a false theorem.

They are included for provenance and reproducibility of the *data*, not of the proof.

## A note on the code itself

These are the scripts as they were actually run, including hard-coded output paths from
the author's machine. They have deliberately not been tidied: the point of archiving them
is provenance, and a cleaned-up script is no longer the one that produced the committed
data. They are not a build step — nothing in `lake build` or in CI invokes them — so they
need not run anywhere else, and the repository builds without them.
