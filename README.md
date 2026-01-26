# SymmetricTensorProof

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".


After following the steps above, you can remove this section from the README file.

## Build and Execution

To build the executable:
```bash
lake build verify_proof
```

The binary will be located at `.lake/build/bin/verify_proof.exe`.

Usage:
```bash
./.lake/build/bin/verify_proof.exe <input_file> <t> <p>
```
Example:
```bash
./.lake/build/bin/verify_proof.exe input.txt 3 17
```

## Verification Details

In `Verification/check.lean`, we perform rigorous rank calculations for the evidence embedding `p` over a finite field using formalized Gaussian Elimination.
Regarding dependency evidence, we verify that for a specified graph $F \in \mathcal{C}_{n,t}$ and a circuit $C$, the condition $C \subseteq F$ holds and that the number of edges satisfies $|E(C)| > c_t(F)$.

## Graph Enumeration

The graph enumeration component allows for the generation of graphs with specific properties.

- **`Spec.lean`**: Defines the mathematically rigorous logic for graph enumeration.
- **`Impl.lean`**: Provides an executable implementation corresponding to the specification.
- **`Correctness.lean`**: Establishes the equivalence between the executable implementation in `Impl.lean` and the rigorous specification in `Spec.lean`.
- **`ByteImpl.lean`**: Offers a more practical and optimized implementation for faster enumeration.
- **`ByteCorrectness.lean`**: Ensures the consistency between the reference `Impl.lean` and the optimized `ByteImpl.lean`.

Note that for graph isomorphism checking (isomorphism deletion), we rely on `nauty` as an axiom.

