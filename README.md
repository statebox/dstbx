# Petri nets in Idris

These are some experiments to see what the current status
of Idris is and how pleasant it works for this kind of stuff.

Conclusion so far: Idris remains most pleasant-to-use DTP-language.

---

```
~/s/dstb (master:61) » idris net.idr                                             21:47
    ____    __     _
   /  _/___/ /____(_)____
   / // __  / ___/ / ___/     Version 0.12.2
 _/ // /_/ / /  / (__  )      http://www.idris-lang.org/
/___/\__,_/_/  /_/____/       Type :? for help

Idris is free software with ABSOLUTELY NO WARRANTY.
For details type :warranty.
Type checking ./net.idr
*net> marking i0
Just [FZ, FS FZ] : Maybe (List (Fin 4))
*net> marking i1
Just [FS FZ, FS (FS FZ)] : Maybe (List (Fin 4))
*net>
Bye bye
```

---

The type `Net (s:Nat) (t:Nat)` is the type of finite petri nets
over `s` number of places with `t` number of transition

For example:

    net : Net 4 4
    net = [
      ([], [0, 1]),
      ([0], [2]),
      ([1], [3]),
      ([2,3], [])
    ]

To create an instance, use the `Instance s t` data structure.

Fire the first transition

    i0 : Inst 4 4
    i0 = Init net 0

Fire another transition

    i1 : Inst 4 4
    i1 = Fire i0 1

We can now get the marking corresponding to the instances

    marking i0
    => Just [0, 1]

    marking i1
    => Just [1, 2]
