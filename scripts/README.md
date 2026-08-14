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
