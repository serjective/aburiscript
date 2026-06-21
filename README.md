<img src="./media/logo.png" width="256px"/>


Aburi, pronounced "Eh-bree," is a C and C++ compiler frontend. It currently lowers source code to LLVM IR, uses LLVM for optimization and final code emission, and exposes a GCC/Clang-like driver named `aburi`.

The project is still early and under active development, but it already supports a substantial C surface and a growing C++ subset including classes, inheritance, virtual dispatch, templates, exceptions, and ABI-aware lowering. Many real world programs and compiler test suites compile and run successfully with Aburi.

The name of the project comes from the town of Aburi, Ghana and its [botanical garden](https://www.instagram.com/aburibotanicalgarden/).

For more information, visit the [Aburi project website](https://serjective.org/aburi).