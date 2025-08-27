


1.

```sml
val df = Controls.add true (name ^ ".diff")
```

```sml
| Special(j as (jop, tyopt, nameopt), vs, cty) =>
  let
    val (vs, tys) = transVals (fn () => false) env vs
  in
    case ExtOps.toString jop of
      ":=" => (Triv vs, cty)
    | _ =>
    (Special((jop, Option.map (transType) tyopt, nameopt),
    vs, transCmpType false cty), cty)
  end
```

```diff
63c63
<                     let crve{Regression1.f} <= ref ():[a]unit [heap] ref
---
>                     let crve{Regression1.f} <= ref ():[a]?
65c65
<                         :=<crve,()>:[w]<>
---
>                         val<crve,()>
```

```
Unhandled Exception:
System.MissingMethodException: Method not found: void System.Object..ctor(object)
[ERROR] FATAL UNHANDLED EXCEPTION: System.MissingMethodException: Method not found: void System.Object..ctor(object)
```

```sml
| Special(j as (jop, tyopt, nameopt), vs, cty) =>
  let
    val (vs, tys) = transVals (fn () => false) env vs
  in
    case ExtOps.toString jop of
      ":=" => (Triv [], MILTy.noeffect [])
    | _ => (Special((jop, Option.map (transType) tyopt, nameopt),
            vs, transCmpType false cty), cty)
  end
```

```diff
63c63
<                     let crve{Regression1.f} <= ref ():[a]unit [heap] ref
---
>                     let crve{Regression1.f} <= ref ():[a]?
65c65
<                         :=<crve,()>:[w]<>
---
>                         val<>
```

```sml
val (vs, tys) = transVals (fn () => false) env vs
val () = print ("Tys: ")
val () = List.app (fn ty => print (MILTy.toString ty ^ " ")) tys
val () = print ("\n")
```

```
Special ref
Tys: unitprod
Special :=
Tys: unitprod[heap] ref unitprod
```

```sml
  | Prod [] => "unitprod"
```

```sml
| Special(j as (jop, tyopt, nameopt), vs, cty) =>
  let
    val (vs, tys) = transVals (fn () => false) env vs
    val () = print ("Tys: ")
    val () = List.app (fn ty => print (MILTy.toString ty ^ " ")) tys
    val () = print ("\n")
  in
    case (ExtOps.toString jop, List.map MILTy.proj tys) of
      (":=", _ :: MILTy.Prod [] :: _) => (Triv [], MILTy.noeffect [])
    | _ => (Special((jop, Option.map (transType) tyopt, nameopt),
                     vs, transCmpType false cty), cty)
  end
```

```sml
structure Regression1 = struct
  fun main () =
    let
      val f = ref ()
      val () = f := ()
      val () = f := print "hello\n"
      val g = ref ((), 1, ())
      val () = g := ((), 2, ())
      val h = ref { a = (), b = 1, c = () }
      val () = h := { a = (), b = 2, c = (print "world\n"; ()) }
    in
      ()
    end
end
```

```
> smlnet.sh Regression1
> mono Regression1.exe
hello
world
```