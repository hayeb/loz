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
* Implement currying
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
        ```shell script
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
* Implement reading code from multiple files
* Implement simple module system
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
* Clean-up AST, should speed up parsing
* ✔ Rework ```Main``` start rule, should be a normal function called ```main```
* I'm using ```clone()``` more than I'd like, due to not bothering with lifetimes
* Benchmark
* Probably use different parser
* Build test suite 
* Fix weird crash with "a-b"


## Usage
The compiler supports reading code from a single file:
```shell script
$ cloz test/test.loz
> Int(1)
```

It currenty does not support any arguments or options :)