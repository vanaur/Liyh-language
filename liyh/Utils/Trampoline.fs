namespace Liyh.Utils

module Trampoline =
    open System

    // From: https://www.fssnip.net/dK/title/Monadic-Trampoline

    type public TrampValue<'T> =
        | DelayValue of Delay<'T>
        | ReturnValue of Return<'T>
        | BindValue of IBind<'T>

    and public ITramp<'T> =
        abstract member Value: TrampValue<'T>
        abstract member Run: unit -> 'T

    and public Delay<'T>(f: unit -> ITramp<'T>) =
        member self.Func = f

        interface ITramp<'T> with
            member self.Value = DelayValue self
            member self.Run() = (f ()).Run()

    and public Return<'T>(x: 'T) =
        member self.Value = x

        interface ITramp<'T> with
            member self.Value = ReturnValue self
            member self.Run() = x

    and public IBind<'T> =
        abstract Bind<'R> : ('T -> ITramp<'R>) -> ITramp<'R>

    and public Bind<'T, 'R>(tramp: ITramp<'T>, f: ('T -> ITramp<'R>)) =
        interface IBind<'R> with
            member self.Bind<'K>(f': 'R -> ITramp<'K>) : ITramp<'K> =
                new Bind<'T, 'K>(tramp, (fun t -> new Bind<'R, 'K>(f t, (fun r -> f' r)) :> _)) :> _

        interface ITramp<'R> with
            member self.Value = BindValue self

            member self.Run() =
                match tramp.Value with
                | BindValue b -> b.Bind(f).Run()
                | ReturnValue r -> (f r.Value).Run()
                | DelayValue d -> (new Bind<'T, 'R>(d.Func(), f) :> ITramp<'R>).Run()

    type public TrampolineBuilder() =
        member self.Return a = new Return<_>(a) :> ITramp<_>

        member self.Bind(tramp, f) =
            new Bind<'t, 'r>(tramp, f) :> ITramp<'r>

        member self.Delay f = new Delay<_>(f) :> ITramp<_>

        member self.TryFinally<'T>(expr: ITramp<'T>, compensation: unit -> unit) : ITramp<'T> =
            new Delay<'T>(fun () ->
                try
                    expr
                finally
                    compensation ())
            :> ITramp<'T>

        member self.ReturnFrom value = value
        member self.Zero() = self.Return()

        member self.Combine<'T, 'R>(expr1: ITramp<'T>, expr2: ITramp<'R>) : ITramp<'R> =
            self.Bind(expr1, (fun (_: 'T) -> expr2))

        member self.TryWith<'T>(expr: ITramp<'T>, handler: exn -> ITramp<'T>) : ITramp<'T> =
            new Delay<'T>(fun () ->
                try
                    expr
                with ex ->
                    handler ex)
            :> ITramp<'T>

    let inline public run (trampoline: ITramp<'T>) = trampoline.Run()

    let public tramp = new TrampolineBuilder()
