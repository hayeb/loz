# LOZ

A small, simple functional programming language. Loosely based on Clean, because I like the syntax. The intention of this project is to get to know Rust, and to finally implement another version of a programming language without getting bogged down in code generation. The compiler is statically typed with support for type inference fot let-bindings.

Does NOT support lazyness and does NOT use graph/term rewriting as basis for evaluation. 

## TODO

### Features
* Implement lists (```[a : [b]]```, or ```[a, b]```)
* Implement algebraic datatypes
    
    ```
    Tree = Node Tree Tree
        | Leaf Int
  
    Maybe = Just a
        | Nothing
    ```
* Implement tail call elimination (in interpreter?)
* Implement floating point numbers:
    * Add Float type
    * Modify parser
    * Determine semantics (probably just use Rust semantics)
* Implement interactive interpreter
    * Implement evaluating expression
    * Implement help
    * Global variables/state?
* Implement records 

    ```
    Person = {
        name :: String,
        phone_numer :: String,
        age :: Int
    }
    ```
* Implement type inference (Hindley-Milner probably)
    * Can leave out type signatures for functions
    * More overloaded operators?
    * Probaby also included type variables
        ```shell script
        find :: [a] a -> Bool
        ```
* Implement mutual recursion
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
    ```shell script
    import lib/types.loz
  
    from lib/types.loz import Person
    ```
* Implement small standard library
    * Reading files
    * Retrieving data from the web
    * ...?

### Technical improvements
* Clean-up AST, should speed up parsing
* I'm using ```clone()``` more than I'd like, due to not bothering with lifetimes
* Benchmark
* Probably use different parser
* Build test suite 
* Fix weird crash with "a-b"


## Usage
The compiler supports reading code from a single file:
```shell script
$ ./loz.exe test/test.loz
> Int(1)
```

It currenty does not support any arguments or options :)