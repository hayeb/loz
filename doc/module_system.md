# The Loz Module System

The module system used by Loz is loosely based on the module system of Clean.

A module is a set of Loz functions in a file.

```text
A/
    B.loz
        > :: f
        > :: g
    D/
        E.loz
            > :: map
            > :: flatten
        F.loz
            > :: zip
            > :: unzip
```
The above results in the above modules:

```
A.B
    f
    g
A.D.E
    map
    flatten
A.D.F
    zip
    unzip
```


Suppose the B.loz file contains the function ```flip```, the _path_ of that function would be ```A.B::flip```.

Functions within a module can reference one another freely.

Functions in module ```A``` can only reference a function ```f``` in module ```B``` when:
1. Module ```B``` exports ```f``` by use of an export rule:
    1. ```export f```
2. Module ```C``` imports ```B::f``` by use of an import rule:
    1. ```import B```
    2. ```from B import f```
    
Modules ```A``` and ```B``` can contains functions of the same name. When both are imported by module ```C```, an error occurs.

This can be solved by way of aliased imports:

```text
from A import f as g, g as h
``` 

Or the entire module can be prefixed:

```text
import A as B
```

