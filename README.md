<img src="./media/logo.png" width="256px"/>

Aburi, pronounced "Eh-bree," is a modern C and C++ compiler. It currently uses LLVM as a backend, with work underway on a native backend (Aburi IR). The project is still early and under heavy development. It includes the Adinkra C++ standard library, which can be used with other compilers like Clang.

The goals of Aburi are the following:

* **Lightweight!** Aburi pulls in no external dependencies other than LLVM. Minimizing memory and CPU overhead is a long-term goal of the project.
* **Feature-Complete!** Almost all the C standard has been implemented. Full C++ compliance is well underway. Aburi can compile demanding C programs such as Ghostscript, Postgres, and even the Linux Kernel, along with a growing selection of Clang `libc++` headers. Many Clang and GCC-specific language extensions are implemented.
* **Fast!** Work is underway for a "fast" mode for debug builds to help with heavy edit-compile-debug workflows. The Adinkra "non-optimized" C++ standard library can already provide 2x-5x speedup in build time when building real C++ programs with Apple Clang.

The name of the project comes from the small town of Aburi in Ghana and the [beautiful botanical gardens](https://www.graphic.com.gh/features/features/aburi-botanical-gardens-tourist-attraction-on-the-mountain.html) located within. "Aburi" also means "mist" in Romanian, meaning one could also call Aburi the "Misty Compiler" 😊


For more information, visit the [Aburi project website](https://serjective.org/aburi).
