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

