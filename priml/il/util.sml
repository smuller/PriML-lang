structure ILUtil :> ILUTIL =
struct

  infixr 9 `
  fun a ` b = a b
  fun I x = x

    open IL
    exception ILUtil of string

    fun mappoly f (Poly (p, x)) = Poly (p, f x)

    (* XXX this should be several pointwise functions for the different syntactic classes, 
       like in CPS. *)
    (* run f on all immediate subexpressions of exp,
       then rebuild it *)
    fun pointwise f exp = 
        (case exp of
             Value v => Value (pwv f v)
           | Jointext el => Jointext (map f el)
           | Record lel => Record (ListUtil.mapsecond f lel)
           | Proj (l, t, e) => Proj(l, t, f e)
           | Get { addr, typ, body, dest } => Get { addr = f addr,
                                                    typ = typ,
                                                    body = f body,
                                                    dest = dest }
           | Raise (t, e) => Raise(t, f e)
           | Handle (e, t, v, handler) => Handle(f e, t, v, f handler)
           | Seq (e1, e2) => Seq (f e1, f e2)
           | Roll (t, e) => Roll (t, f e)
           | Unroll e => Unroll (f e)
           | Tag (e1, e2) => Tag (f e1, f e2)
           | Inject(t, l, e) => Inject (t, l, Option.map f e)
           | Throw (e1, e2) => Throw(f e1, f e2)
           | Primapp(po, el, tl) => Primapp (po, map f el, tl)
           | App (ff, el) => App (f ff, map f el)
           | Sumcase (t, e, v, lel, def) => Sumcase (t, f e, v,
                                                     ListUtil.mapsecond f lel,
                                                     f def)
           | Untag {typ, obj, target, bound, yes, no} => Untag {typ=typ,
                                                                obj = f obj,
                                                                target = f obj,
                                                                bound = bound,
                                                                yes = f yes,
                                                                no = f no }
           | Letcc (v, t, e) => Letcc (v, t, f e)
           | Let(Do e1, e2) => pointwise f (Seq(e1, e2))
           | Let(Tagtype v, e) => Let(Tagtype v, f e)
           | Let(Letsham vtvp, rest) => 
               Let(Letsham
                   (mappoly (fn (v, t, va) => (v, t, pwv f va)) vtvp),
                    f rest)
           | Let(Newtag(v, t, vv), e) => Let(Newtag (v, t, vv), f e)
           | Let(Bind (b, vtep), rest) => Let(Bind
                                              (b, mappoly (fn (v, t, e) =>
                                                           (v, t, f e)) vtep), 
                                              f rest)
                    )
    and pwv f v =
      (case v of
         Fns l =>
           Fns (map (fn {name, arg, dom, cod, body, inline, recu, total} =>
                     {name=name,
                      inline=inline,
                      recu=recu,
                      total=total,
                      arg=arg,
                      dom=dom,
                      cod=cod,
                      body=f body}) l)
       (* FIXME |  =>  *)
           )

    (* nb. does not handle capture/shadowing. *)
(*  unused, wrong
    fun tsubste s exp =
        let 
            val self = tsubste s
            fun sub t = Subst.tsubst s t

            fun tsubstv v =
              (case v of
                 (* anything that has a t in it *)
                 Polyvar({worlds, tys, var}) => 
                   Polyvar({worlds=worlds, tys = map sub tys, var=var})
              | Fns l => 
                   Fns `
                   map (fn {name, arg, dom,
                            cod, body, inline,
                            recu, total} =>
                        {name=name,
                         arg=arg,
                         dom=map sub dom,
                         cod=sub cod,
                         recu=recu,
                         body=self body,
                         inline=inline,
                         total=total}) l

                   (* FIXME ... *)
               | Int _ => v
               | String _ => v)

        in
            case exp of
                Value v => Value (tsubstv v)
                (* allow delayed *)
              | Get { addr, typ, body, dest } => Get { addr = self addr,
                                                       typ = sub typ,
                                                       body = self body,
                                                       dest = dest }
              | Raise(t, e) => Raise(sub t, self e)
              | Proj(l, t, e) => Proj(l, sub t, self e)
              | Roll(t, e) => Roll(sub t, self e)
              | Untag {typ, obj, target, bound, yes, no} => Untag { typ = sub typ,
                                                                    obj = self obj,
                                                                    target = self obj,
                                                                    bound = bound,
                                                                    yes = self yes,
                                                                    no = self no }
              | Primapp(po, el, tl) =>
                    Primapp(po, map self el, map sub tl)
              | Sumcase(t, obj, v, vel, def) =>
                    Sumcase(sub t, self obj, v,
                            ListUtil.mapsecond self vel,
                            self def)
              | Letcc(v, t, e) => Letcc(v, sub t, self e)
              | Let(Newtag(v,t,vv), e) =>
                    Let(Newtag(v, sub t, vv), self e)
              | Let(Val vtep, e) =>
                    Let(Val (mappoly (fn (v,t,e) => (v, sub t, self e)) vtep),
                        self e)
              (* FIXME is this all of them? *)
              (* otherwise recurse *)
              | _ => pointwise self exp
        end
*)

    fun duplicate e = pointwise duplicate e

    fun unevar (Evar (ref (Bound t))) = unevar t
      | unevar (Evar _) = raise ILUtil "didn't expect unset evar!"
      | unevar t = t

end