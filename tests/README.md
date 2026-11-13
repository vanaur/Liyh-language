# Tests

This folder contains the positive test suite of the language (i.e. they all must pass). All the implemented features of the language are covered and combined with others. Most files implements a specific set of tests centred around a particular set of features.

The main file is [Testsuite.liyh](Testsuite.liyh). You can run the tests simply using this command:

```bash
$ liyh run Testsuite.liyh
```

> [!IMPORTANT]
> Not all the tests present in these files are representative of what may be considered idiomatic in Liyh, but they test the edge cases, the interactions between the features, the behaviour of the type checker and the compiler. Nevertheless, they also represent a good but condensed overview of the language too!


## Tiny Standard Library (TSL)

For the purpose of these tests, a small standard library has been implemented (the file [TSL.liyh](TSL.liyh) for **T**iny **S**tandard **L**ibrary). If you want to test the language, this library is the stand-in until the real standard library is available. It covers basic arithmetic and types (`List`, `Option` and `Result`).

---

**Note:** Gemini 3.8 Flash was used to help organise and implement some of these tests. Most tests were written by hand by the author beforehand.
