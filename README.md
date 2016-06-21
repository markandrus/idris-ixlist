ixlist
======

_This is a work-in-progress._

This library provides `IxList`, a list indexed by its elements.

```idr
> the (IxList [1, 2, 3]) [1, 2, 3]
[1, 2, 3] : IxList [1, 2, 3]
```

We aim for near-API compatibility with Idris's `List` data type and related
functions.
