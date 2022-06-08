# LOZ

A small, simple functional programming language. Loosely based on Clean/Haskell, because I like the syntax. 
The intention of this project is to get to know Rust, and to finally implement another version of a programming language without getting bogged down in code generation.
For now, there is a simple interpreter that directly executes the compiled Loz code.
The compiler is statically typed with support for type inference in let-bindings.

Does NOT support laziness and does NOT use graph/term rewriting as basis for evaluation. 

## TODO

* Rename language?

### Features
* ✔ Implement defining lambda functions and passing them around
    ```
    map :: [a] (a -> b) -> [b]
    map [] _ = []
    map [b : bs] f = [f b : map bs f]
  
    Main = map [1, 2, 3] (\a. a + 1)
  ```
* ✔ Implement currying
* ✔ Implement record field accessor operator ```.```
* Implement tail call elimination (in interpreter?)
* Implement interactive interpreter
    * Implement evaluating expression
    * Implement help
    * Global variables/state?
* Implement type inference (Hindley-Milner probably)
    * ✔ Can leave out type signatures for functions
    * More overloaded operators?
    * ✔ Probaby also included type variables
        ```
        find :: [a] a -> Bool
        ```
* ✔ Implement mutual recursion
    ```
    f :: Int -> Int
    f 0 = 0
    f n = g (n - 1)
  
    g :: Int -> Int
    g 0 = 1
    g n = f (n - 1)
    ```
* ✔ Implement reading code from multiple files
* ✔ Implement simple module system
    ```
    import lib/types.loz
  
    from lib/types.loz import Person
    ```
* Implement small standard library
    * Reading files
    * Retrieving data from the web
    * ...?
* Implement checking match completeness

### Technical improvements
* ✔ Clean-up AST, should speed up parsing
* ✔ Rework ```Main``` start rule, should be a normal function called ```main```
* ✔ I'm using ```clone()``` more than I'd like, due to not bothering with lifetimes
* Benchmark
* Probably use different parser
* ✔ Build test suite 
* Fix weird crash with "a-b"


## Usage

TODO: This should be updated..
The compiler supports reading code from a single file:
```shell script
$ cloz test/test.loz
> Int(1)
```

It currenty does not support any arguments or options :)

## Development on Windows
1. Install Visual Studio Build Tools
2. Check if link.exe points to Build Tools version, not the version provided by Git for Windows
3. `choco install StrawberryPerl`
4. `choco install cmake.install`
5. `cargo install llvmenv`
6. `llvmenv init`
7. Download the desired sources from LLVM GitHub (for instance, https://github.com/llvm/llvm-project/archive/refs/tags/llvmorg-11.1.0.zip)
8. Extract contents to directory $LLVM_SRC_DIR
9. Add local entry for llvmenv replace $LLVM_SRC_DIR with actual source directory:
   ```toml
   [local-11]
   path = "$LLVM_SRC_DIR"
   target = ["X86"]
   ```
10. Build from source:
   ```
   llvmenv build-entry local-11
   ```
   This can take some time :)
11. Export LLVM prefix environment variable
   ```
   setx LLVM_SYS_110_PREFIX "C:\Users\user.name\AppData\Roaming\llvmenv\local-11"
   ```
12. `cargo build` should work now!